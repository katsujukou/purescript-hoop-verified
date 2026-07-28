(**
 * The Hoop effect runtime, whose architecture is based on a CEK-like abstract machine:
 *
 *   - C = Control      ... the current computation node
 *   - E = Environment  ... the evidence environment used for handler dispatch
 *   - K = Kontinuation ... a defunctionalized continuation represented
 *                          as an explicit stack of frames
 *
 * The C component is the AST of a computation. The K component records 
 * *what to do in the next frame*. The machine executes a program by 
 * repeatedly transitioning between configurations of the form <C, E, K>.
 *
 * In a conventional CEK machine, E maps variables to values. In Hoop, lexical
 * environments are already captured by PureScript/JavaScript closures. We 
 * therefore repurpose E as an evidence environment that maps each handled 
 * operation to evidence identifying its prompt —- thestack frame thatmarks the 
 * boundary for continuation capture -— and the environment outsidethat prompt.
 *)
module Hoop.Runtime

open FStar.List.Tot

(**
 * The handlers table. keyed with two strings (eff, op) which represents
 * the name of effect and operation, respectively.
 *)
type handlers (cl: Type) = list (string & string & cl)

(**
 * The `comp_tree` is the C-part of the CEK machine and represents the AST
 * of the whole program, which is the chain of `Hoop`-monadic `bind`
 * and `pure`, corresponds to Op and Var node respectively, PLUS the 
 * effect-related primitives such as `handle`/`perform`/`resume`.
 * Polymorphic in two types: v is the type of computation inputs/outputs
 * and the `cl` the type of handlers. Basically, `cl` may be understood as
 * something like 
 *   ```
 *   list v       -> (v -> comp_tree) -> comp_tree
 *   ^^^^ payloads     ^ continuation
 *  ```
 * but we cannot put this function type directly in the constructor argument
 * because doing so violates the [*strictly positive rule.*](https://fstar-lang.org/tutorial/book/part2/part2_inductive_type_families.html#strictly-positive-definitions)
 *)
noeq
type comp_tree (v: Type) (cl: Type) =
  | Op : c: comp_tree v cl -> fn: (v -> comp_tree v cl) -> comp_tree v cl
  | Var : value: v -> comp_tree v cl
  | Perform : eff: string -> op: string -> payload: list v -> comp_tree v cl
  | Handle : hs: handlers cl -> pure: option (v -> comp_tree v cl) -> body: comp_tree v cl
    -> comp_tree v cl
  // `Resumed` node is machine-internal and should never exported to the PS-world;
  // it is inserted by the machine at the head of delimited continuation when it is loaded as 
  // the next instruction as the result of firing `continue k` in the handler clause.
  | Resumed : frames: list (frame v cl) -> value: v -> comp_tree v cl

(**
 * The `frame` is the K-part of the CEK machine and represents the *defunctionalized* continuation.
 *)
and frame (v: Type) (cl: Type) =
  | BindF : fn: (v -> comp_tree v cl) -> frame v cl
  | PromptF : hs: handlers cl -> pure: option (v -> comp_tree v cl) -> frame v cl

type stack (v: Type) (cl: Type) = list (frame v cl)

(** The machine state *)
noeq
type state (v: Type) (cl: Type) =
  | Done : value: v -> state v cl
  | Step : c: comp_tree v cl -> k: stack v cl -> state v cl
  // Unhandled effect operation exception which should never occur
  // as long as the runtime is sound
  | Stuck : eff: string -> op: string -> state v cl

// ------------------------------------------------------------------ //

let rec lookup_clause (#cl: Type) (hs: handlers cl) (eff op: string) : option cl =
  match hs with
  | [] -> None
  | (e, o, c) :: rest -> if e = eff && o = op then Some c else lookup_clause rest eff op

// Finds the prompt containing the handlers responsible for the given action.
// Splits the stack at the prompt and return both: `(captured, below)`.
// The first Capture the delimited continuation —
// every frame above the matching prompt, prompt included — so
// resuming reinstalls the handler (deep-handler semantics).
// Tail-recursive
let rec find_prompt_aux
    (#v #cl : Type)
    (eff op : string)
    (soFar k : stack v cl)
  : Tot (option (stack v cl & cl & stack v cl)) 
        (decreases k)
  = match k with
    | [] -> None
    | hd::tl ->
      match hd with
      | PromptF hs ret ->
          ( match lookup_clause hs eff op with
            | Some c -> Some (rev (hd::soFar), c, tl)
            | None -> find_prompt_aux eff op (hd::soFar) tl
          )
    | _ -> find_prompt_aux eff op (hd::soFar) tl
  
let find_prompt
    (#v #cl : Type)
    (eff op : string)
    (k : stack v cl)
  : option (stack v cl & cl & stack v cl)
  = find_prompt_aux eff op [] k

(**
 * The small-step semantics of the machine.
 *)
let step
    (#v #cl: Type)
    (apply: (cl -> list v -> (v -> comp_tree v cl) -> comp_tree v cl))
    (s: state v cl)
  : state v cl 
  = match s with
    | Done _ -> s
    | Stuck _ _ -> s
    | Step c k -> 
      match c with
      | Op comp fn -> Step comp (BindF fn :: k)
      | Handle hs pure body -> Step body (PromptF hs pure :: k)
      | Perform eff op payload ->
        // Find the first handler responsible to the action identified as `(eff, op)`
        (match find_prompt eff op k with
          | None -> Stuck eff op
          // `below` is  
          | Some (captured, clause, below) ->
            // Processing `Perform` node updates the next instruction by 
            // the computation returned by feeding the handler payloads of the 
            // action. The continuation `below` is packed in `Resumed` node
            // enabling to come back to the code after perform when `continue k`
            // is called.
            Step (apply clause payload (fun x -> Resumed captured x)) below)
      | Var value ->
        (match k with
          | [] -> Done value
          | (BindF fn)::rest -> Step (fn value) rest
          | (PromptF _ pure)::rest ->
            //  Matching this case means we are to evaluate
            // ```purs
            //   with (handler { ... }) do
            //     pure v 
            // ```
            // i.e. we immediately leave the handlers' scope without
            // performing any action, so we safely dispose the prompt.
            (match pure with
              | Some fn -> Step (fn value) rest
              | None -> Step (Var value) rest
            )
        )
      // `Resumed` node, built during processing the *Perform*, captures
      // the delimited continuation `kont`; conceptually, `continue k v` 
      // works as `pure v >>= k` where `k` carries *what to do after leaving 
      // handler clause*
      | Resumed kont value -> Step (Var value) (kont @ k)

// The transitive closure of `step`. The `fuel` argument 
// ensures termination of the recursion. This function is meant
// to be used only for stating theorems and proofs and hence 
// the return has ghost effect `GTot`.    
let rec steps
      (#v #cl: Type)
      (apply: (cl -> list v -> (v -> comp_tree v cl) -> comp_tree v cl))
      (fuel: nat)
      (s: state v cl)
    : GTot (state v cl) =
  if fuel = 0
  then s
  else
    match s with
    | Done _ -> s
    | Stuck _ _ -> s
    | Step _ _ -> steps apply (fuel - 1) (step apply s)

(**
 * The transitive closure of `step`
 * Unlike the `steps`, this is meant to be extracted 
 * and compiled to .ml and .js
 *)
let rec run
    (#v #cl: Type)
    (apply: (cl -> list v -> (v -> comp_tree v cl) -> comp_tree v cl))
    (s: state v cl)
  : Div 
      (state v cl)
      (requires True)
      (ensures fun r-> Done? r \/ Stuck? r)
  = match s with
    | Done _ -> s
    | Stuck _ _ -> s
    | Step _ _ -> run apply (step apply s)

let load (#v #cl: Type) (c: comp_tree v cl) : state v cl = Step c []

