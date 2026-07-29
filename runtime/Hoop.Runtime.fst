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
 * environments are already captured by PureScript/JavaScript closures. We therefore
 * repurpose E as an evidence environment that maps each handled operation to evidence
 * identifying its prompt —- the stack frame which marks the boundary for continuation
 * capture -— and the environment outside that prompt.
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
  | Op:
      c:comp_tree v cl ->
      fn:(v -> comp_tree v cl) ->
      comp_tree v cl
  | Var:
      value:v ->
      comp_tree v cl
  | Perform:
      eff:string ->
      op:string ->
      payload:list v ->
      comp_tree v cl
  | Handle: 
      hs:handlers cl ->
      pure:option (v -> comp_tree v cl) ->
      body:comp_tree v cl ->
      comp_tree v cl
  // `Resumed` node is machine-internal and should never exported to the PS-world;
  // it is inserted by the machine at the head of delimited continuation when it is loaded as 
  // the next instruction as the result of firing `continue k` in the handler clause.
  | Resumed:
      frames: list (frame v cl) ->
      value: v ->
      comp_tree v cl

(**
 * The `frame` is the K-part of the CEK machine and represents the *defunctionalized* continuation.
 *)
and frame (v: Type) (cl: Type) =
  | BindF:
      fn:(v -> comp_tree v cl) ->
      frame v cl
  | PromptF:
      hs:handlers cl ->
      pure:option (v -> comp_tree v cl) ->
      frame v cl

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

// Is this frame responsible for the action identified as `(eff, op)`?
let rec lookup_clause (#cl: Type) (hs: handlers cl) (eff op: string) : option cl =
  match hs with
  | [] -> None
  | (e, o, c) :: rest -> if e = eff && o = op then Some c else lookup_clause rest eff op

let handles
    (#v #cl: Type)
    (eff op: string)
    (f: frame v cl)
  : GTot (b:bool { b <==> (PromptF? f /\ Some? (lookup_clause (PromptF?.hs f) eff op) )})
  = match f with
    | PromptF hs _ -> Some? (lookup_clause hs eff op)
    | BindF _ -> false

(**
 * **Handled in a stack**: at least one frame of the stack `k` handles the action identified
 * as `(eff, op)`. This is the existentially quantified counterpart of `handles`, and it
 * supplies the vocabulary in which the absence of a `Stuck` state is phrased below.
 *)
let handled_in
    (#v #cl : Type)
    (eff op : string)
    (k: stack v cl)
  : GTot prop
  = exists (f: frame v cl).
      (f `memP` k /\ handles eff op f)

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
  : Tot (o: option (stack v cl & cl & stack v cl) { handled_in eff op k <==> Some? o }) 
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
  : o: option (stack v cl & cl & stack v cl) { handled_in eff op k <==> Some? o }
  = find_prompt_aux eff op [] k

let apply_t (v cl : Type) = cl -> list v -> (v -> comp_tree v cl) -> comp_tree v cl

let well_scoped
    (#v #cl : Type)
    (apply: apply_t v cl)
  : prop 
  = True

(**
 * The small-step semantics of the machine.
 *)
let step
    (#v #cl: Type)
    (apply: apply_t v cl)
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


(**
 * **The multi-step relation**: the iteration of `step`, i.e. its transitive closure
 * cut off at `fuel` transitions.
 *
 * The `fuel` argument is there for termination only. It is not part of the semantics:
 * the machine is not "charged" for a transition in any meaningful sense, and no theorem
 * below reads anything into the particular number handed in. It merely lets a partial
 * function—the machine may well diverge—be written down as a total one, which is what
 * F* insists on. Once a terminal state (`Done` or `Stuck`) is reached the remaining fuel
 * is simply burnt without effect; `steps_terminal` states exactly that, and
 * `steps_stable` turns it into the statement that the answer does not depend on how
 * generous the caller was.
 *
 * The `GTot` effect is deliberate. `steps` exists to state theorems and to exercise the
 * machine inside `assert_norm`; it is never meant to run in the PureScript/JavaScript
 * world, where `Hoop.Runtime.run` (a `Div` function, and the one that is extracted)
 * plays that role. Marking it ghost lets the effect system, rather than a comment,
 * enforce that separation: `steps` cannot leak into extracted code, and indeed it
 * produces none.
 *)
let rec steps
      (#v #cl: Type)
      (apply: apply_t v cl)
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

let one_more_step 
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl { Step? s })
    (r: state v cl)
  : Lemma 
      (requires exists (n:nat). r == steps apply n (step apply s))
      (ensures (exists (m:nat). r == steps apply m s))
  = eliminate exists (n:nat). r == steps apply n (step apply s)
    returns _
    with _. 
      introduce exists (m:nat). r == steps apply m s
      with (n + 1) and ()

let no_more_steps
    (#v #cl : Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires Done? s \/ Stuck? s)
      (ensures exists (n:nat). s == steps apply n s)
  = introduce exists (n:nat). s == steps apply n s 
    with 0 
    and ()

(**
 * The transitive closure of `step`.
 * Unlike `steps`, this function is designed to be extracted 
 * and compiled into `.ml` and `.js`.
 *
 * The return type carries the following important lemma in an intrinsic style:
 *   The final state returned by `run` is reachable within a finite number of iterations of `step`.
 * Thanks to this, we can transfer all properties proved about `steps` over to `run`.
 *)
let rec run
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : Div 
      (state v cl)
      (requires True)
      (ensures fun r -> 
          (Done? r \/ Stuck? r) /\
          exists (n:nat). r == steps apply n s)
  = match s with
    | Done _ -> no_more_steps apply s; s
    | Stuck _ _ -> no_more_steps apply s; s
    | Step _ _ -> 
        let r = run apply (step apply s) in 
        one_more_step apply s r;
        r

let load (#v #cl: Type) (c: comp_tree v cl) : state v cl = Step c []

