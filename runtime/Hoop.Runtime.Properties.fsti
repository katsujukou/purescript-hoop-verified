module Hoop.Runtime.Properties

open Hoop.Runtime
open FStar.List.Tot

let find_prompt_t
    (v:Type)
    (cl:Type)
  = eff: string ->
    op: string ->
    k: stack v cl ->
    GTot (o:option (stack v cl & cl & stack v cl) { handled_in eff op k <==> Some? o })

(**
 * **The preservation of stack**: appending the captured and the rest of stack
 * reproduces original one, i.e. `cap @ below == k`
 *
 * This lemma ensures the `find_prompt` indeed *splits* the stack;
 * no dropping, adding or moving any frame.
 *)
let find_prompt_partitions_correctness
    (#v #cl: Type)
    (find_prompt: find_prompt_t v cl)
    (eff op: string)
    (k: stack v cl)
  : prop
  = handled_in eff op k ==>
      (let Some (cap, _, below) = find_prompt eff op k in
          cap @ below == k
      )
      
val find_prompt_partitions
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (find_prompt_partitions_correctness find_prompt eff op k)

(**
 * **The Lemma about the last frame of the captured continuation**:
 * The captured segments are non-empty, and their *final* element is precisely
 * the `PromptF` frame which holds the selected operation clause.
 *
 * This serves as the foundation for *deep handler semantics*: the handler is
 * re-installed upon resumption, allowing the continuation to perform the same
 * effect again inside it.
 *)
let find_prompt_last_correctness
    (#v #cl : Type)
    (find_prompt: find_prompt_t v cl)
    (eff op : string)
    (k : stack v cl)
  : prop
  = handled_in eff op k ==>
      (let Some (cap, c, _) = find_prompt eff op k in
          // captured continuation must not be empty
          Cons? cap /\
          // captured continuation has the prompt as the last element
          PromptF? (last cap) /\
          // and that prompt is for the same handler clause 
          lookup_clause (PromptF?.hs (last cap)) eff op == Some c
      )

val find_prompt_last
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma 
    (find_prompt_last_correctness find_prompt eff op k)

(**
 * Innermost Lemma:
 * The prompt found by `find_prompt` is the one capable of handling the 
 * given action that is closest to the current position (i.e., the top of the stack).
 *
 * This lemma guarantees the correctness of handler shadowing: 
 * when a handler scope for the same action is nested within another, 
 * `perform` always selects the innermost surrounding handler.
 *)
let find_prompt_innermost_correctness
    (#v #cl: Type)
    (find_prompt: find_prompt_t v cl)
    (eff op: string)
    (k: stack v cl)
  : prop
  = handled_in eff op k ==>
      (let Some (cap, _, _) = find_prompt eff op k in
          // The captured continuation stack is non-empty.
          (Cons? cap) /\
          // The selected prompt is the unique innermost handler for this action.
          ~(handled_in eff op (init cap))
      )

val find_prompt_innermost
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (find_prompt_innermost_correctness (find_prompt #v #cl) eff op k)

(**
 * Corollary: the meaning of handled_in.
 *)
let find_prompt_none
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (~(handled_in eff op k) <==>
          (forall (f: frame v cl). memP f k ==> not (handles eff op f)))
  = ()
// -------------------------------------- //

(**
 * The soundness of `lookup_clause`:
 * If `lookup_clause hs eff op` returns `Some c`, then the triple `(eff, op, clause)`
 * should indeed be an element of the handlers table `hs`.
 * In other words, `lookup_clause` never forges the handler clause.
 *
 * Together with `find_prompt_last`, ensures that:
 * the returned clause is indeed a member of handlers installed by the prompt at the bottom of
 * the captured continuation.
 *)
let lookup_clause_soundness
    (#cl : Type)
    (hs: handlers cl)
    (eff op : string)
  : prop
  = match lookup_clause hs eff op with
    | None -> False
    | Some c -> memP (eff, op, c) hs

val lookup_clause_memP
    (#cl: Type)
    (hs: handlers cl)
    (eff op: string)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures (lookup_clause_soundness hs eff op))

(**
 * **The completeness of `lookup_clause`**:
 * if `lookup_clause` returns `None` then the handlers table never has
 * an entry identified as `(eff, op)`
 *
 * This is the frame-layer equivalent of `find_prompt_none`. It guarantees that
 * if a prompt's `handles` check returns `false`, it is because the prompt truly lacks
 * that effect, not because the search somehow missed it. Only with this completeness
 * can the innermost property (`find_prompt_innermost`) validly claim that
 * *no handler is ever bypassed*.
 *)
let lookup_clause_completeness
    (#cl : Type)
    (hs : handlers cl)
    (eff op : string)
  : prop
  = None? (lookup_clause hs eff op) ==>
      forall (c: cl). ~(memP (eff, op, c) hs)

val lookup_clause_none
    (#cl: Type)
    (hs: handlers cl)
    (eff op: string)
  : Lemma
      (requires None? (lookup_clause hs eff op))
      (ensures lookup_clause_completeness hs eff op)

//------------------------//

(**
 * Perform Progress Lemma:
 * Executing `perform eff op payload` within a handler context capable of 
 * handling `(eff, op)` transitions the machine into the following state:
 *
 * - The term under evaluation becomes the computation obtained by applying 
 *   the payload (along with the captured continuation) to the corresponding 
 *   handler clause for `(eff, op)` in that context.
 * - The stack state becomes the remaining continuation below the target prompt.
 *
 *)
 val step_perform
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures
          (let Some (captured, clause, below) = find_prompt eff op k in
              // 1. The next computation is the handler clause fed with the payload of the action
              // and with the delimited continuation and the machine keeps running on `below`.
              (step apply (Step (Perform eff op payload) k) ==
                  Step (apply clause payload (fun x -> Resumed captured x)) below) /\
              // 2. Stack is preserved ... this is the direct consequence of `find_prompt_partitions`
              captured @ below == k))

(**
 * Perform Termination Lemma:
 * Stepping a `perform` node gets stuck if and only if it is executed 
 * outside the context of a handler that can handle the performed action.
 *
 * Conversely, a `perform` operation will never get stuck as long as it is 
 * executed within a context that can handle the given action (eff, op). 
 * This key property serves as a foundation for our subsequent proofs 
 * regarding general progress and machine soundness.
 *)
val step_perform_stuck
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl)
  : Lemma
      (~(handled_in eff op k) <==>
          step apply (Step (Perform eff op payload) k) == Stuck eff op)

(**
 * Corollary (Progress of Resumed):
 * Stepping `Resumed v kont` under the stack `c` transitions the machine 
 * into the following state:
 *
 * - The term under evaluation becomes `Var v`, which represents the value 
 *   passed to the `continue` invocation.
 * - The stack state becomes `kont @ c`, meaning the captured continuation 
 *   is appended back onto the current stack.
 *
 * *Note*: While this statement itself is nearly trivial, combining it with
 * "The Lemma about the last frame of the captured continuation" naturally
 * yields the deep handler semantics, where the prompt is re-installed onto
 * the stack upon every `continue` invocation.
 *)
let step_resumed
    (#v #cl : Type)
    (apply: apply_t v cl)
    (comp : comp_tree v cl)
    (cc : stack v cl)
  : Lemma
      (Resumed? comp ==>
        step apply (Step comp cc) ==
          Step (Var (Resumed?.value comp)) ((Resumed?.frames comp) @ cc))
  = ()

// Some more trivial facts which shape the transition rules
// i.e. *operational semanthics* of the machine.

let step_op
    (#v #cl: Type)
    (apply: apply_t v cl)
    (c: comp_tree v cl)
    (fn: v -> comp_tree v cl)
    (k: stack v cl)
  : Lemma (step apply (Step (Op c fn) k) == Step c (BindF fn :: k))
  = ()

let step_handle
    (#v #cl: Type)
    (apply: apply_t v cl)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma (step apply (Step (Handle hs ret body) k) == Step body (PromptF hs ret :: k))
  = ()

let step_var_done
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
  : Lemma (step apply (Step (Var value) ([] <: stack v cl)) == Done value)
  = ()

let step_var_bind
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
    (fn: v -> comp_tree v cl)
    (rest: stack v cl)
  : Lemma (step apply (Step (Var value) (BindF fn :: rest)) == Step (fn value) rest)
  = ()

let step_var_prompt
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (rest: stack v cl)
  : Lemma
      (step apply (Step (Var value) (PromptF hs ret :: rest)) ==
        (match ret with
          | Some r -> Step (r value) rest
          | None -> Step (Var value) rest))
  = ()

let step_var_prompt_identity
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
    (hs: handlers cl)
    (rest: stack v cl)
  : Lemma (step apply (Step (Var value) (PromptF hs None :: rest)) == Step (Var value) rest)
  = ()

let handle_installs
    (#v #cl: Type)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (k: stack v cl)
    (eff op: string)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures handled_in eff op (PromptF hs ret :: k))
  = ()

let stack_weakening
    (#v #cl: Type)
    (eff op: string)
    (f: frame v cl)
    (k: stack v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures handled_in eff op (f :: k))
  = ()

//------------------------//

(**
 * Lemma of step fixpoint
 *)
val steps_terminal
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires Done? s \/ Stuck? s)
      (ensures steps apply n s == s)

(**
 * The lemma of step-additivity
 *)
val steps_add
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n m: nat)
    (s: state v cl)
  : Lemma
      (ensures steps apply (n + m) s == steps apply m (steps apply n s))

(**
 * Corollary (Stability of Step):
 * For any natural number `m` and state `s`, if `steps m s` evaluates to `Done`, 
 * then `steps (n + m) s == steps m s` holds for any natural number `n`.
 *
 * This property is a direct consequence of the Fixed-Point Lemma and the 
 * Step Additivity Lemma.
 *)
val steps_stable
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n m: nat)
    (s: state v cl)
  : Lemma
      (requires Done? (steps apply n s))
      (ensures steps apply (n + m) s == steps apply n s)

// ------------------------------------------------------------------ //
//  Well-scopedness: the defining equations                            //
// ------------------------------------------------------------------ //

(**
 * `Hoop.Runtime.ws` is defined by recursion on a step index rather than on the
 * computation tree, for the reason spelled out where it is defined: the return
 * clause of `Handle` is an `option (v -> comp_tree v cl)`, and F* has no subterm
 * axiom reaching under it, so the structural definition one would like to write
 * cannot be shown to terminate.
 *
 * The eight lemmas of this section are what makes that a matter of bookkeeping
 * rather than of substance. Each is an `<==>`, and together they are exactly the
 * clauses of the structural definition: `ws` at a `Var` holds, `ws` at a
 * `Perform` is availability of the action, `ws` at an `Op` is `ws` of both parts,
 * and so on. Nothing in the development below ever unfolds `ws_n`; it works
 * through these equations alone. In that sense `ws` *is* the naive definition,
 * and the step index never appears in a statement anyone reads.
 *
 * They are also the reason `ws` may be treated as abstract: this interface
 * mentions neither `ws_n` nor `wf_stack_n`, so a client reasons about `ws` only
 * through the equations, the congruence lemmas, and the theorems below.
 *)

(** **A value is well scoped anywhere**: it fires nothing. *)
val ws_var
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (x: v)
  : Lemma (ws cok a (Var x <: comp_tree v cl))

(**
 * **A `Perform` is well scoped exactly when its action is available**. This is
 * the only clause of `ws` that can fail, and hence the entire content of the
 * predicate: everything else merely propagates it through the tree.
 *)
val ws_perform
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (eff op: string)
    (payload: list v)
  : Lemma (ws cok a (Perform eff op payload <: comp_tree v cl) <==> a eff op)

(**
 * **`Op` distributes**: `c >>= fn` is well scoped exactly when `c` is and every
 * branch of `fn` is. The environment does not change across a bind — a bind
 * installs no handler.
 *)
val ws_op
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (c: comp_tree v cl)
    (fn: v -> comp_tree v cl)
  : Lemma (ws cok a (Op c fn) <==> (ws cok a c /\ (forall (x: v). ws cok a (fn x))))

(**
 * **`Handle` extends the environment for its body only**: the body may use
 * whatever the table declares, on top of what was already in scope, whereas the
 * clauses and the return clause run *outside* the prompt they belong to and so
 * see only `a`.
 *
 * That asymmetry is not an accident of the definition, it is the scoping rule of
 * the language. A clause is invoked after `step` has cut the stack at its own
 * prompt and thrown that prompt away for the duration; a return clause is
 * invoked by `step_var_prompt`, which pops the prompt first. Neither can rely on
 * its own handler being installed, and `ws` says so.
 *)
val ws_handle
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
  : Lemma
      (ws cok a (Handle hs ret body) <==>
        (ws cok (extend hs a) body /\ handler_ok cok a hs /\ ret_ws cok a ret))

(**
 * **A `Resumed` node is well scoped exactly when the continuation it carries is
 * well formed**. The node holds no computation of its own; it is the machine's
 * way of splicing a captured stack segment back on, so its obligation is that of
 * a stack.
 *)
val ws_resumed
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (frames: stack v cl)
    (x: v)
  : Lemma (ws cok a (Resumed frames x) <==> wf_stack cok a frames)

(** **The empty stack is well formed**: it suspends nothing. *)
val wf_stack_nil
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
  : Lemma (wf_stack cok a ([] <: stack v cl))

(**
 * **A `BindF` frame contributes nothing to the environment**: the suspended
 * continuation is judged in the environment of the frames below it, unchanged.
 *)
val wf_stack_bind
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (fn: v -> comp_tree v cl)
    (rest: stack v cl)
  : Lemma
      (wf_stack cok a (BindF fn :: rest) <==>
        ((forall (x: v). ws cok (can_in_with rest a) (fn x)) /\ wf_stack cok a rest))

(**
 * **A `PromptF` frame owes for its table and its return clause**, both judged
 * *below* the prompt — the same rule as `ws_handle`, which is what makes the two
 * agree when `step_handle` turns one into the other.
 *)
val wf_stack_prompt
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (rest: stack v cl)
  : Lemma
      (wf_stack cok a (PromptF hs ret :: rest) <==>
        (handler_ok cok (can_in_with rest a) hs /\
         ret_ws cok (can_in_with rest a) ret /\
         wf_stack cok a rest))

// ------------------------------------------------------------------ //
//  Congruence in the environment                                      //
// ------------------------------------------------------------------ //

(**
 * **Well-scopedness only sees which actions an environment offers**, not how the
 * environment was built.
 *
 * Availability environments are functions, so the ones the machine computes are
 * equal pointwise but almost never syntactically: pushing a `BindF` frame yields
 * `can_in (BindF fn :: k)`, a different closure from `can_in k` although it offers
 * exactly the same actions. Every preservation proof below therefore ends with a
 * congruence step, and these lemmas are it. The hypothesis `clause_ok_congr cok` is
 * inherited by `handler_ok` and propagated through the whole predicate.
 *)
val clauses_ok_cong
    (#cl: Type)
    (cok: clause_ok_t cl)
    (a1 a2: can_perform)
    (hs: handlers cl)
  : Lemma
      (requires clause_ok_congr cok /\ equiv_can a1 a2)
      (ensures handler_ok cok a1 hs <==> handler_ok cok a2 hs)

val ws_cong
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a1 a2: can_perform)
    (c: comp_tree v cl)
  : Lemma
      (requires clause_ok_congr cok /\ equiv_can a1 a2)
      (ensures ws cok a1 c <==> ws cok a2 c)

val wf_stack_cong
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a1 a2: can_perform)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ equiv_can a1 a2)
      (ensures wf_stack cok a1 k <==> wf_stack cok a2 k)

// ------------------------------------------------------------------ //
//  How the environment reacts to the stack surgery `step` performs    //
// ------------------------------------------------------------------ //

(** **Pushing a `BindF` frame changes nothing**: a bind installs no handler.
    This is the environment-level reading of `step_op`. *)
val av_bind
    (#v #cl: Type)
    (fn: v -> comp_tree v cl)
    (k: stack v cl)
    (a: can_perform)
  : Lemma (equiv_can (can_in_with (BindF fn :: k) a) (can_in_with k a))

(** **Pushing a `PromptF` frame extends the environment by its table**, which is
    the environment-level reading of `step_handle`, and matches to the letter the
    extension `ws_handle` grants the body of the corresponding `Handle`. That the
    two agree is what carries well-scopedness across that transition. *)
val av_prompt
    (#v #cl: Type)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (k: stack v cl)
    (a: can_perform)
  : Lemma (equiv_can (can_in_with (PromptF hs ret :: k) a) (extend hs (can_in_with k a)))

(** **Concatenation of stacks composes environments**: running on `k1` stacked on
    `k2` offers what `k1` offers on top of what `k2` does. Needed for the
    `Resumed` transition, which splices a captured segment back on. *)
val av_append
    (#v #cl: Type)
    (k1 k2: stack v cl)
    (a: can_perform)
  : Lemma (equiv_can (can_in_with (k1 @ k2) a) (can_in_with k1 (can_in_with k2 a)))

// ------------------------------------------------------------------ //
//  Splitting and joining a well-formed stack                          //
// ------------------------------------------------------------------ //

(**
 * **Well-formedness is compositional along `@`**: a concatenated stack is well
 * formed exactly when the lower part is, and the upper part is well formed in
 * the environment the lower part offers.
 *
 * This is the workhorse of the two transitions that take a stack apart or put
 * one back together — `Perform`, which cuts at a prompt, and `Resumed`, which
 * splices the cut segment back on. Read left to right it justifies the cut; read
 * right to left, the splice.
 *)
val wf_stack_append
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (k1 k2: stack v cl)
    (a: can_perform)
  : Lemma
      (requires clause_ok_congr cok)
      (ensures wf_stack cok a (k1 @ k2) <==> (wf_stack cok (can_in_with k2 a) k1 /\ wf_stack cok a k2))

(**
 * **The clause table of a prompt buried in a well-formed stack is well scoped
 * below that prompt**. Combined with `find_prompt_last` — which says the prompt
 * `step` selects really does hold the clause it hands to `apply` — this is what
 * supplies the `cok (can_in below) clause` premise that `apply_ok` demands.
 *)
val wf_stack_split_prompt
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (k1: stack v cl)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (k2: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_stack cok a (k1 @ (PromptF hs ret :: k2)))
      (ensures handler_ok cok (can_in_with k2 a) hs)

// ------------------------------------------------------------------ //
//  Preservation of the machine invariant, one transition at a time    //
// ------------------------------------------------------------------ //

(**
 * The five lemmas that follow are the five branches of `step`, each shown to
 * take a well-formed state to a well-formed state. They are stated separately
 * rather than inlined into `step_preserves_wf` because they are of very
 * different weights — `pres_var` is immediate, `pres_perform` is the whole
 * argument — and keeping them apart keeps each SMT query small.
 *)

(** **Op**: descending into the left of a bind, with the rest parked on the
    stack. The pushed frame changes no environment, so both halves of `ws_op`
    land where they must. *)
val pres_op
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (inner: comp_tree v cl)
    (fn: v -> comp_tree v cl)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (Op inner fn) k))
      (ensures wf_state cok (step apply (Step (Op inner fn) k)))

(** **Handle**: the extension `ws_handle` grants the body is exactly the one
    `av_prompt` says the pushed frame provides. *)
val pres_handle
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (Handle hs ret body) k))
      (ensures wf_state cok (step apply (Step (Handle hs ret body) k)))

(** **Var**: a value meets the top frame. Whichever frame it is, its obligation
    was recorded against the environment of the frames below, which is precisely
    the environment the machine now runs in. *)
val pres_var
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (value: v)
    (k: stack v cl)
  : Lemma
      (requires wf_state cok (Step (Var value <: comp_tree v cl) k))
      (ensures wf_state cok (step apply (Step (Var value <: comp_tree v cl) k)))

(** **Resumed**: the captured segment is spliced back on. Well-formedness of the
    join follows from `wf_stack_append`, the environments matching by `av_append`. *)
val pres_resumed
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (captured: stack v cl)
    (value: v)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (Resumed captured value) k))
      (ensures wf_state cok (step apply (Step (Resumed captured value) k)))

(**
 * **Perform**: the interesting one, and the only branch that could get stuck.
 *
 * Well-scopedness of the `Perform` says the action is available on `k`, which by
 * definition of `can_in` means `find_prompt` succeeds — so the `Stuck` branch is
 * already out. What remains is that the state the machine moves to is well
 * formed, and that is assembled from three facts proved elsewhere: the stack
 * splits as `captured @ below` (`find_prompt_partitions`); the prompt owning the
 * clause is the last frame of `captured` (`find_prompt_last`), whence
 * `wf_stack_split_prompt` gives `cok (can_in below) clause`; and the captured segment,
 * being well formed over `below`, makes `fun x -> Resumed captured x` a well
 * scoped continuation there (`ws_resumed`). `apply_ok` then delivers the clause
 * body, well scoped in `can_in below`, which is where the machine continues.
 *)
val pres_perform
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\
                wf_state cok (Step (Perform eff op payload) k))
      (ensures wf_state cok (step apply (Step (Perform eff op payload) k)))

(**
 * **Preservation**: one transition of a well-formed machine leaves it well
 * formed. The five branches above, assembled.
 *)
val step_preserves_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
      (ensures wf_state cok (step apply s))

(**
 * **Progress, one step**: a well-formed machine does not wedge. This is
 * preservation read against the `Stuck` clause of `wf_state`, which is `False`.
 *
 * Compare `step_perform_stuck`, which reduces the absence of `Stuck` to *some
 * frame on the stack handles the action*. That reduction left open the question
 * of why a handler should be there at all; well-scopedness is the answer, and
 * this lemma is where the two meet.
 *)
val step_progress
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
      (ensures ~(Stuck? (step apply s)))

// ------------------------------------------------------------------ //
//  Progress                                                           //
// ------------------------------------------------------------------ //

(** **Preservation along a whole run**: the invariant is an invariant of `steps`,
    not merely of `step`. Induction on the fuel. *)
val steps_preserves_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
      (ensures wf_state cok (steps apply n s))

(**
 * **Progress**: a well-formed machine never gets stuck, however long it runs.
 *
 * This is the theorem the `Stuck` constructor was always waiting for. Its
 * comment in `Hoop.Runtime` says the state *should never occur as long as the
 * runtime is sound*; here that hope is discharged, against a precise reading of
 * *sound* — the program is well scoped, and the FFI's `apply` respects
 * well-scopedness.
 *)
val progress
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
      (ensures ~(Stuck? (steps apply n s)))

(** **Loading a well-scoped program yields a well-formed state**: the empty stack
    is well formed and offers exactly the empty environment. *)
val load_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (c: comp_tree v cl)
  : Lemma
      (requires clause_ok_congr cok /\ ws cok (can_nothing ()) c)
      (ensures wf_state cok (load c))

(**
 * **From the invariant to the precondition of `run`**: `Hoop.Runtime.run`
 * demands `never_stuck`, and this is what produces it.
 *
 * `run` cannot be given `wf_state cok s` directly as its precondition, because
 * `run` lives in `Hoop.Runtime` and would then need `step_preserves_wf`, which
 * lives here — modules do not go round in circles. Phrasing `run`'s
 * precondition as *this run never reaches `Stuck`* breaks the knot: that
 * property is closed under `step` by inspection, so `Hoop.Runtime` stays
 * self-contained, while the substance of the argument is supplied from here by
 * these two lemmas.
 *)
val wf_never_stuck
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
      (ensures never_stuck apply s)

(**
 * **The entry point**: a well-scoped program may be handed to `run`, and comes
 * back `Done`.
 *
 * Read together with the type of `run`, this is the end-to-end statement of the
 * development: if the PureScript side only ever builds programs whose `perform`s
 * sit inside a matching `with`-block, and its clause interpreter respects
 * `apply_ok`, then the machine either diverges or returns a value — it never
 * reports an unhandled operation.
 *)
val load_never_stuck
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (c: comp_tree v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ ws cok (can_nothing ()) c)
      (ensures never_stuck apply (load c))
