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

// ------------------------------------------------------------------ //
//  Well-scopedness                                                    //
// ------------------------------------------------------------------ //

let can_perform = eff:string -> op:string -> bool

let can_nothing () : GTot can_perform = fun _ _ -> false

// Extending with handlers
let extend (#cl: Type) (hs: handlers cl) (c: can_perform) : GTot can_perform =
  fun eff op -> Some? (lookup_clause hs eff op) || c eff op

let can_in_with
    (#v #cl: Type)
    (k: stack v cl)
    (c: can_perform)
  : GTot can_perform
  = fun eff op -> Some? (find_prompt eff op k) || c eff op

let can_in (#v #cl: Type) (k: stack v cl) : GTot can_perform = can_in_with k (can_nothing ())

 // Pointwise equality of effect-capability
let equiv_can (can1 can2: can_perform) : prop = forall (eff op: string). can1 eff op == can2 eff op

(**
 * **The clause judgement**: `cok can c` reads *the handler clause `c` fires no
 * action outside `can`*.
 *
 * Clauses are opaque to the machine — `cl` is instantiated with a PureScript
 * closure — so nothing can be *computed* about them here; well-scopedness of
 * clauses is therefore left as a parameter of the whole development rather than
 * baked in. Instantiating `cok := fun _ _ -> True` recovers the simpler
 * judgement in which clauses are only allowed to touch the world through the
 * continuation they are handed. The extra generality is what makes room for a
 * clause that *delegates* — one that performs an action of its own, to be
 * handled further out — since such a clause is well scoped exactly when the
 * action it fires is available where the clause runs.
 *)
let clause_ok_t (cl: Type) = can_perform -> cl -> prop

(**
 * The clause judgement respects `equiv_can`: it may not distinguish two
 * environments offering the same actions. This is the only assumption the 
 * development makes about `clause_ok_t`. It is needed because the environments
 * the machine computes are equal pointwise but rarely syntactically: 
 * `can (BindF fn :: k)` and `can k`, for instance, are two different closures 
 * denoting the same set of actions.
 *)
let clause_ok_congr (#cl: Type) (cok: clause_ok_t cl) : prop =
  forall (can1 can2: can_perform) (c: cl). equiv_can can1 can2 ==> (cok can1 c <==> cok can2 c)

(** **A well-scoped handler table**: every clause it holds is well scoped in `can`. *)
let handler_ok
    (#cl: Type)
    (cok: clause_ok_t cl)
    (can: can_perform)
    (hs: handlers cl) : prop =
  forall eff op clause. 
      lookup_clause hs eff op == Some clause ==> cok can clause

(**
 * **Well-scopedness, step-indexed**: `ws_n n cok can c` is the well-scopedness of
 * `c` in the environment `can`, inspected to depth `n`; `wf_stack_n` is its counterpart
 * for stacks. `ws` and `wf_stack` below quantify the index away, and are what one
 * actually reasons with.
 *
 * *Why the index is there.* The definition one would like to write is the plain
 * structural recursion on `c` — the shape recovered by the equation lemmas in
 * `Hoop.Runtime.Properties`. F* will not accept it. `comp_tree` stores
 * continuations as functions, and the subterm order `<<` does give
 * `Op?.fn d y << d` for a field of type `v -> comp_tree v cl`; but the return
 * clause of `Handle` has type `option (v -> comp_tree v cl)`, and there the
 * chain breaks. F* knows `Some?.v (Handle?.pure d) << d`, yet the last link,
 * `h y << h` for a bare function `h`, is not an axiom — it is generated only for
 * a constructor *field*, not for an arbitrary function value. So
 * `Some?.v (Handle?.pure d) y << d` is unavailable and the recursive call under
 * the return clause cannot be shown to terminate. Dropping the return clause
 * from the definition is not an option either: a handler whose body and table
 * are impeccable but whose *return clause* fires an unhandled action does get
 * the machine stuck, so an invariant blind to it could not support progress.
 *
 * *Why nothing is lost.* The index is pure proof scaffolding: `decreases n`
 * discharges termination, and `ws` closes over every `n`. The resulting
 * predicate satisfies exactly the equations of the structural definition — that
 * is precisely the content of `ws_op`, `ws_handle`, `ws_resumed`, `wf_stack_bind`
 * and `wf_stack_prompt` in `Hoop.Runtime.Properties`, each an `<==>`. Those lemmas
 * are the only interface to `ws` that the rest of the development uses, so `ws`
 * *is* the naive definition, in the only sense that matters. Note also that the
 * unfolding at index `0` is `True` rather than `False`: this keeps `ws_n`
 * monotone downwards in `n`, so that closing over all `n` is a conjunction of
 * approximations rather than a limit that could collapse.
 *)
private
let rec ws_n (#v #cl: Type) (n: nat) (cok: clause_ok_t cl) (can: can_perform) (c: comp_tree v cl)
  : GTot prop (decreases %[n; 1; 0])
  = if n = 0 then True
    else
      match c with
      | Var _ -> True
      | Perform eff op _ -> can eff op == true
      | Op inner fn ->
          ws_n (n - 1) cok can inner /\ (forall (x: v). ws_n (n - 1) cok can (fn x))
      | Handle hs ret body ->
          ws_n (n - 1) cok (extend hs can) body /\
          handler_ok cok can hs /\
          (match ret with
            | None -> True
            | Some r -> forall (x: v). ws_n (n - 1) cok can (r x))
      | Resumed frames _ -> wf_stack_n n cok can frames

(**
 * **Well-formedness of a stack, step-indexed**: every computation suspended in a
 * frame is well scoped in the environment offered by the part of the stack
 * *below* that frame — which is exactly the environment in which the machine
 * will eventually resume it.
 *
 * The two clauses differ in the obvious way: a `BindF` frame contributes nothing
 * to the environment, whereas a `PromptF` frame installs its table, so the
 * frames above it see more than the frames below.
 *)
and wf_stack_n (#v #cl: Type) (n: nat) (cok: clause_ok_t cl) (can: can_perform) (k: stack v cl)
  : GTot prop (decreases %[n; 0; length k])
  = if n = 0 then True
    else
      match k with
      | [] -> True
      | BindF fn :: rest ->
          (forall (x: v). ws_n (n - 1) cok (can_in_with rest can) (fn x)) /\ wf_stack_n n cok can rest
      | PromptF hs ret :: rest ->
          handler_ok cok (can_in_with rest can) hs /\
          (match ret with
            | None -> True
            | Some r -> forall (x: v). ws_n (n - 1) cok (can_in_with rest can) (r x)) /\
          wf_stack_n n cok can rest

(** **Well-scopedness**: `c` fires no action outside `can`, at any depth. *)
let ws (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (c: comp_tree v cl) : GTot prop =
  forall (n: nat). ws_n n cok can c

(** **Well-formedness of a stack**: every suspended computation it holds is well
    scoped where it will be resumed, at any depth. *)
let wf_stack (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (k: stack v cl) : GTot prop =
  forall (n: nat). wf_stack_n n cok can k

(** **The obligation carried by a return clause**, named rather than written out
    so that no `match` ever appears inside the statement of a lemma — F* has a
    hard time discharging those. *)
let ret_ws (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (ret: option (v -> comp_tree v cl))
  : GTot prop
  = match ret with
    | None -> True
    | Some r -> forall (x: v). ws cok can (r x)

(* ------------------------------------------------------------------ *)
(*  Peeling the step index                                             *)
(*                                                                     *)
(*  `ws_n` and `wf_stack_n` are `private`: the index is an artefact of  *)
(*  the definition and no module outside this one is meant to mention   *)
(*  it. The lemmas below are the only place it is ever peeled.          *)
(*  `Hoop.Runtime.Properties` assembles them into the `<==>` equations  *)
(*  of the structural definition, and the rest of the development works *)
(*  through those alone.                                               *)
(*                                                                     *)
(*  Each forward direction needs a hint -- from `forall n. ws_n n cok   *)
(*  can c` the solver has to be told to look at index `n + 1`, which is *)
(*  where the head constructor is unfolded -- while each backward       *)
(*  direction goes through on its own, except under an `option`, where  *)
(*  the `match` has to be split by hand.                               *)
(* ------------------------------------------------------------------ *)

let ws_perform_eq (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                  (eff op: string) (payload: list v)
  : Lemma (ws cok can (Perform eff op payload <: comp_tree v cl) <==> can eff op == true)
  = assert (ws_n 1 cok can (Perform eff op payload <: comp_tree v cl) <==> can eff op == true)

let ws_op_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
              (c: comp_tree v cl) (fn: v -> comp_tree v cl)
  : Lemma (requires ws cok can (Op c fn))
          (ensures ws cok can c /\ (forall (x: v). ws cok can (fn x)))
  = assert (forall (n: nat). ws_n (n + 1) cok can (Op c fn))

let ws_handle_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                  (ret: option (v -> comp_tree v cl)) (body: comp_tree v cl)
  : Lemma (requires ws cok can (Handle hs ret body))
          (ensures ws cok (extend hs can) body /\ handler_ok cok can hs /\ ret_ws cok can ret)
  = assert (ws_n 1 cok can (Handle hs ret body));
    assert (forall (n: nat). ws_n (n + 1) cok can (Handle hs ret body));
    (match ret with
      | None -> ()
      | Some r -> assert (forall (x: v) (n: nat). ws_n n cok can (r x)))

#push-options "--split_queries always"
let ws_handle_bwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                  (ret: option (v -> comp_tree v cl)) (body: comp_tree v cl)
  : Lemma (requires ws cok (extend hs can) body /\ handler_ok cok can hs /\ ret_ws cok can ret)
          (ensures ws cok can (Handle hs ret body))
  = match ret with
    | None -> ()
    | Some r -> assert (forall (x: v) (n: nat). ws_n n cok can (r x))
#pop-options

let ws_resumed_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                   (frames: stack v cl) (x: v)
  : Lemma (requires ws cok can (Resumed frames x)) (ensures wf_stack cok can frames)
  = assert (forall (n: nat). ws_n (n + 1) cok can (Resumed frames x))

let wf_stack_bind_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                      (fn: v -> comp_tree v cl) (rest: stack v cl)
  : Lemma (requires wf_stack cok can (BindF fn :: rest))
          (ensures (forall (x: v). ws cok (can_in_with rest can) (fn x)) /\
                   wf_stack cok can rest)
  = assert (forall (n: nat). wf_stack_n (n + 1) cok can (BindF fn :: rest))

let wf_stack_prompt_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                        (ret: option (v -> comp_tree v cl)) (rest: stack v cl)
  : Lemma (requires wf_stack cok can (PromptF hs ret :: rest))
          (ensures handler_ok cok (can_in_with rest can) hs /\
                   ret_ws cok (can_in_with rest can) ret /\
                   wf_stack cok can rest)
  = assert (wf_stack_n 1 cok can (PromptF hs ret :: rest));
    assert (forall (n: nat). wf_stack_n (n + 1) cok can (PromptF hs ret :: rest));
    (match ret with
      | None -> ()
      | Some r -> assert (forall (x: v) (n: nat). ws_n n cok (can_in_with rest can) (r x)))

#push-options "--split_queries always"
let wf_stack_prompt_bwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                        (ret: option (v -> comp_tree v cl)) (rest: stack v cl)
  : Lemma (requires handler_ok cok (can_in_with rest can) hs /\
                    ret_ws cok (can_in_with rest can) ret /\
                    wf_stack cok can rest)
          (ensures wf_stack cok can (PromptF hs ret :: rest))
  = match ret with
    | None -> ()
    | Some r -> assert (forall (x: v) (n: nat). ws_n n cok (can_in_with rest can) (r x))
#pop-options

(** **The clause judgement is congruent**, which is `clause_ok_congr` read
    through `handler_ok`. Stated here rather than one module up because the
    step-indexed congruence below needs it. *)
let handler_ok_cong (#cl: Type) (cok: clause_ok_t cl) (can1 can2: can_perform) (hs: handlers cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures handler_ok cok can1 hs <==> handler_ok cok can2 hs)
  = introduce forall (c: cl). (cok can1 c <==> cok can2 c)
    with assert (clause_ok_congr cok)

(* Congruence has to be proved at every index before it can be closed over,
   hence a pair of step-indexed lemmas mirroring `ws_n` / `wf_stack_n`. *)
private
let rec ws_n_cong (#v #cl: Type) (n: nat) (cok: clause_ok_t cl) (can1 can2: can_perform)
                  (c: comp_tree v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures ws_n n cok can1 c <==> ws_n n cok can2 c)
          (decreases %[n; 1; 0])
  = if n = 0 then ()
    else
      match c with
      | Var _ -> ()
      | Perform _ _ _ -> ()
      | Op inner fn ->
          ws_n_cong (n - 1) cok can1 can2 inner;
          introduce forall (x: v).
            (ws_n (n - 1) cok can1 (fn x) <==> ws_n (n - 1) cok can2 (fn x))
          with ws_n_cong (n - 1) cok can1 can2 (fn x)
      | Handle hs ret body ->
          assert (equiv_can (extend hs can1) (extend hs can2));
          ws_n_cong (n - 1) cok (extend hs can1) (extend hs can2) body;
          handler_ok_cong cok can1 can2 hs;
          (match ret with
            | None -> ()
            | Some r ->
              introduce forall (x: v).
                (ws_n (n - 1) cok can1 (r x) <==> ws_n (n - 1) cok can2 (r x))
              with ws_n_cong (n - 1) cok can1 can2 (r x))
      | Resumed frames _ -> wf_stack_n_cong n cok can1 can2 frames

and wf_stack_n_cong (#v #cl: Type) (n: nat) (cok: clause_ok_t cl) (can1 can2: can_perform)
                    (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures wf_stack_n n cok can1 k <==> wf_stack_n n cok can2 k)
          (decreases %[n; 0; length k])
  = if n = 0 then ()
    else
      match k with
      | [] -> ()
      | BindF fn :: rest ->
          assert (equiv_can (can_in_with rest can1) (can_in_with rest can2));
          wf_stack_n_cong n cok can1 can2 rest;
          introduce forall (x: v).
            (ws_n (n - 1) cok (can_in_with rest can1) (fn x) <==>
             ws_n (n - 1) cok (can_in_with rest can2) (fn x))
          with ws_n_cong (n - 1) cok (can_in_with rest can1) (can_in_with rest can2) (fn x)
      | PromptF hs ret :: rest ->
          assert (equiv_can (can_in_with rest can1) (can_in_with rest can2));
          wf_stack_n_cong n cok can1 can2 rest;
          handler_ok_cong cok (can_in_with rest can1) (can_in_with rest can2) hs;
          (match ret with
            | None -> ()
            | Some r ->
              introduce forall (x: v).
                (ws_n (n - 1) cok (can_in_with rest can1) (r x) <==>
                 ws_n (n - 1) cok (can_in_with rest can2) (r x))
              with ws_n_cong (n - 1) cok (can_in_with rest can1) (can_in_with rest can2) (r x))

let ws_cong_eq (#v #cl: Type) (cok: clause_ok_t cl) (can1 can2: can_perform) (c: comp_tree v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures ws cok can1 c <==> ws cok can2 c)
  = introduce forall (n: nat). (ws_n n cok can1 c <==> ws_n n cok can2 c)
    with ws_n_cong n cok can1 can2 c

let wf_stack_cong_eq (#v #cl: Type) (cok: clause_ok_t cl) (can1 can2: can_perform) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures wf_stack cok can1 k <==> wf_stack cok can2 k)
  = introduce forall (n: nat). (wf_stack_n n cok can1 k <==> wf_stack_n n cok can2 k)
    with wf_stack_n_cong n cok can1 can2 k

(**
 * **The machine invariant**: the control component is well scoped in the
 * environment its own stack offers, and the stack is well formed at top level.
 *
 * `Stuck` is ruled out outright — that is the whole point. `Hoop.Runtime.Properties`
 * shows this predicate is preserved by `step` (`step_preserves_wf`), whence a
 * well-formed state never reaches `Stuck` however long it runs (`progress`).
 *)
let wf_state (#v #cl: Type) (cok: clause_ok_t cl) (s: state v cl) : GTot prop =
  match s with
  | Done _ -> True
  | Stuck _ _ -> False
  | Step c k -> ws cok (can_in k) c /\ wf_stack cok (can_nothing ()) k

(**
 * **The condition imposed on the FFI parameter `apply`**: a clause well scoped in
 * `can`, applied to a payload and to a continuation itself well scoped in `can`,
 * yields a computation well scoped in `can`.
 *
 * This one is *not* provable inside F*, and is not meant to be. `apply` is the
 * boundary: it is supplied by the handwritten OCaml in `runtime/ml/hoop_ffi.ml`,
 * where it calls out to an arbitrary PureScript closure whose body F* never
 * sees. `apply_ok` is therefore an assumption on that boundary — the obligation
 * the *PureScript* side must discharge, by construction of its `Hoop` monad, for
 * the progress theorem to apply to a real run. It appears here only as a
 * hypothesis of the theorems in `Hoop.Runtime.Properties`, never as something
 * this module claims.
 *)
let apply_ok (#v #cl: Type) (apply: apply_t v cl) (cok: clause_ok_t cl) : prop =
  forall (can: can_perform) (c: cl) (payload: list v) (kf: v -> comp_tree v cl).
    (cok can c /\ (forall (x: v). ws cok can (kf x))) ==> ws cok can (apply c payload kf)

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
 * **Stuck-freedom along a run**: however long the machine is left to run from
 * `s`, it never reaches `Stuck`.
 *
 * This is the precondition `run` carries, and it is the *conclusion* of the
 * progress development rather than one of its ingredients: `Hoop.Runtime.Properties`
 * derives it from well-scopedness (`wf_never_stuck`, `load_never_stuck`), which
 * is the form a caller is expected to use. Stating `run`'s precondition this way
 * rather than as `wf_state cok s` directly is what keeps this module free of any
 * dependency on the proofs — `run` needs the invariant to be closed under
 * `step`, and for `never_stuck` that is immediate (`never_stuck_step` below),
 * whereas for `wf_state` it is `step_preserves_wf`, which lives one module up
 * and cannot be referred to from here.
 *
 * Being phrased with `steps`, it is `GTot`, hence erased: it constrains the
 * caller without leaving a trace in the extracted code.
 *)
let never_stuck
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : GTot prop
  = forall (n: nat). ~(Stuck? (steps apply n s))

(** Reading the invariant at the current state: index `0` of `never_stuck`. *)
let never_stuck_now
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires never_stuck apply s)
      (ensures ~(Stuck? s))
  = assert (steps apply 0 s == s)

(** The invariant is closed under `step`: a run from `step apply s` is a suffix
    of a run from `s`. *)
let never_stuck_step
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl { Step? s })
  : Lemma
      (requires never_stuck apply s)
      (ensures never_stuck apply (step apply s))
  = introduce forall (n: nat). ~(Stuck? (steps apply n (step apply s)))
    with assert (steps apply (n + 1) s == steps apply n (step apply s))

(**
 * The transitive closure of `step`.
 * Unlike `steps`, this function is designed to be extracted
 * and compiled into `.ml` and `.js`.
 *
 * The return type carries two lemmas in an intrinsic style:
 *
 *   1. The final state returned by `run` is reachable within a finite number of
 *      iterations of `step`. Thanks to this, we can transfer all properties
 *      proved about `steps` over to `run`.
 *   2. That state is `Done`. The machine cannot come back with `Stuck`, and it
 *      cannot come back still running. This is where the well-scopedness
 *      development is cashed in: the precondition `never_stuck apply s` is
 *      exactly what `Hoop.Runtime.Properties.load_never_stuck` produces out of
 *      `ws cok (can_nothing ()) c` for the program `c` the caller loaded.
 *
 * The `Stuck` case is thereby unreachable and no branch of the match names it,
 * so none survives extraction. It is folded into the catch-all rather than
 * omitted outright: `runtime/ml/hoop_ffi.ml` sits outside the type system and
 * may hand in a state this module's precondition does not actually cover, and a
 * catch-all returns such a state to the FFI — which reports the unhandled
 * operation — where an incomplete match would raise `Match_failure` instead.
 *)
let rec run
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl { never_stuck apply s })
  : Div
      (state v cl)
      (requires True)
      (ensures fun r ->
          Done? r /\
          (exists (n:nat). r == steps apply n s))
  = match s with
    | Step _ _ ->
        never_stuck_step apply s;
        let r = run apply (step apply s) in
        one_more_step apply s r;
        r
    | _ ->
        never_stuck_now apply s;
        no_more_steps apply s;
        s

let load (#v #cl: Type) (c: comp_tree v cl) : state v cl = Step c []

