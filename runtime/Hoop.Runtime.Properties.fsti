module Hoop.Runtime.Properties

open Hoop.Runtime
open FStar.List.Tot

let find_prompt_t
    (v:Type)
    (cl:Type)
  = eff: string ->
    op: string ->
    k: stack v cl ->
    GTot (option (stack v cl & cl & stack v cl))

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
  = Some? (find_prompt eff op k) ==>
      (let Some (cap, _, below) = find_prompt eff op k in
          cap @ below == k
      )
val find_prompt_partitions
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures find_prompt_partitions_correctness (find_prompt #v #cl) eff op k)
(**
 * **Captured segments end with the prompt inclusive**:
 * The captured segments are non-empty, and their *final* element is precisely
 * the `PromptF` frame which holds the selected operation clause.
 *
 * This serves as the foundation for **deep handler semantics**. The behavior upon resumption
 * diverges depending on whether the capture cuts *before* the prompt (shallow)
 * or *includes* the prompt itself (deep):
 *   - Under shallow semantics, the resumed continuation is no longer under that handler's scope.
 *   - Under deep semantics, the handler is re-installed upon resumption, allowing the continuation
 *     to perform the same effect again inside it.
 * Hoop adopts the deep semantics approach, and this lemma solidifies this design choice
 * on the F* side.
 *
 * At the same time, this property asserts that "the returned clause is exactly the one looked up
 * from the handler table of the trailing prompt in the captured segment"
 * (`lookup_clause hs eff op == Some c`). It formalizes the guarantee that the clause
 * does not mismatch with the prompt that re-installs it.
 *)
let find_prompt_last_correctness
    (#v #cl : Type)
    (find_prompt: find_prompt_t v cl)
    (eff op : string)
    (k : stack v cl)
  : prop
  = Some? (find_prompt eff op k) ==>
      (let Some (cap, c, _) = find_prompt eff op k in
          (Cons? cap /\
            ( match last cap with
              | PromptF hs _ -> lookup_clause hs eff op == Some c
              | BindF _ -> False
            )
          )
      )
val find_prompt_last
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures (find_prompt_last_correctness (find_prompt #v #cl) eff op k))
(**
 * **Innermost lemma**:
 * No frame in the captured segment before the tail (the handler's own prompt)
 * handles the given (eff, op).
 *
 * This underpins the scoping mechanics of effect handlers. A `perform` must resolve to
 * the innermost capable handler. This lemma ensures that no handling prompt is hidden
 * inside the cut segment; in other words, *no handler is ever bypassed*.
 *
 * Why this matters to the runtime:
 *   This property guarantees proper shadowing when handlers for the same effect are nested.
 *   If this invariant breaks, scope leakage occurs—for instance, an operation might bypass
 *   an inner `Reader` and incorrectly reach an outer one.
 *
 * Note that this statement applies specifically to `init cap` (the captured segment minus the tail).
 * The tail prompt itself is omitted because it is the actual handler. Its existence (`Cons? cap`)
 * is guaranteed by `find_prompt_last` (in the proof, the properties of `last` are extracted
 * before driving the induction).
 *)
let find_prompt_innermost_correctness
    (#v #cl: Type)
    (find_prompt: find_prompt_t v cl)
    (eff op: string)
    (k: stack v cl)
  : prop
  = (Some? (find_prompt eff op k)) ==>
      (let Some (cap, _, _) = find_prompt eff op k in
        (Cons? cap) /\
          forall (f: frame v cl).
            memP f (init cap) ==> not (handles eff op f)
          )
val find_prompt_innermost
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures (find_prompt_innermost_correctness (find_prompt #v #cl) eff op k))
(**
 * **Characterization of Stuck**:
 * `find_prompt` returns `None` if and only if no frame on the stack handles the given (eff, op).
 *
 * Both directions of `<==>` are meaningful:
 *   - (==>) If the search fails, there truly was no handler available.
 *     Since `step` returns `Stuck eff op` upon receiving `None`, this guarantees
 *     "no false positives for Stuck"—meaning the runtime will never accidentally
 *     throw an unhandled exception when a valid handler actually exists.
 *   - (<==) If at least one handler exists, the search is guaranteed to return `Some`.
 *     This ensures no handler is ever missed or overlooked, preventing accidental Stuck states.
 *
 * This property provides type-theoretic backing for the claim that "Stuck never occurs
 * as long as the runtime is sound" (as noted in the comments for `Stuck` in Hoop.Runtime.fst).
 * In other words, to prove the absence of a Stuck state, the problem can be reduced
 * simply to showing that a valid handler resides on the stack.
 *)
let find_prompt_none_correctness
    (#v #cl : Type)
    (find_prompt: find_prompt_t v cl)
    (eff op : string)
    (k: stack v cl)
  : prop
  = None? (find_prompt eff op k) <==>
      (forall (f: frame v cl). memP f k ==> not (handles eff op f))
val find_prompt_none
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (ensures
        find_prompt_none_correctness (find_prompt #v #cl) eff op k)

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
  = Some? (lookup_clause hs eff op) ==>
      (let Some c = lookup_clause hs eff op
      in memP (eff, op, c) hs)

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

(** The soundness of step on perform *)
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
              // 2. Stack is preserved
              captured @ below == k))

(**
 * **Characterization of Stuck at the level of `step`**:
 * the machine gets stuck on `Perform eff op payload` if and only if no frame of the stack
 * handles the given (eff, op). This carries `find_prompt_none` over from the search function
 * to the transition function itself.
 *
 * Both directions of `<==>` are meaningful:
 *   - (<==) `Stuck ==> ~(handled_in eff op k)`: if the machine returned `Stuck`, then the
 *     stack truly held no frame capable of handling that action, i.e. **there are no false
 *     positives for Stuck**. Seen from the PureScript user's side, this rules out the worst
 *     conceivable behavior—being told *Unhandled effect operation* even though the handler
 *     had been installed correctly. In practice this is the more important direction.
 *   - (==>) `~(handled_in eff op k) ==> Stuck`: if not a single frame can handle the action,
 *     the machine does get stuck, i.e. **nothing slips through**. An unhandled operation is
 *     never silently let past.
 *
 * Why this matters to the runtime:
 *   Read contrapositively, the lemma says that as soon as one capable handler sits anywhere
 *   on the stack, `step` does not return `Stuck`. That is the entry point for a future
 *   *progress* theorem, stating that a well-formed machine never wedges.
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
 *
 * Although this corollary is almost self-evident, it remains valuable to establish.
 * This is because, combined with the `find_prompt_last` lemma, it guarantees that
 * the prompt selected on perform is contained within the captured stack segment and
 * reinstalled on resume, which amounts to nothing less than deep handler semantics.
 *)
val step_resumed
    (#v #cl : Type)
    (apply: apply_t v cl)
    (comp : comp_tree v cl { Resumed? comp })
    (cc : stack v cl)
  : Lemma
      (step apply (Step comp cc) ==
        Step (Var (Resumed?.value comp)) ((Resumed?.frames comp) @ cc))

(**
 * When the continuation captured by `perform` is resumed on top of `below` (left by `step_perform`), 
 * the stack is perfectly restored to `k`. Because the next computation transitions to `Var x`, 
 * it becomes identical to the state where the value `x` has just been returned directly after the `perform`.
 *
 * Effectively, when paired with `step_perform`, we can state:
 *
 *   Step (Perform eff op payload) k
 *     --step-->  Step (apply clause payload (fun x -> Resumed captured x)) below
 *                (The clause triggers `continue k x`)
 *     --step-->  Step (Var x) k          (* Back to the original stack *)
 *
 * This directly establishes the formal definition of "capture and resumption canceling each other out."
 *)
val capture_resume_roundtrip
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
    (x: v)
    (apply: apply_t v cl)
  : Lemma
      (requires (handled_in eff op k))
      (ensures
          (let Some (captured, _, below) = find_prompt eff op k in
            step apply (Step (Resumed captured x) below) == Step (Var x) k))

(**
 * **The Op transition**: the left-hand side of a monadic bind is evaluated first, with
 * a `BindF` frame pushed to hold the rest. `Op c fn` is the tree shape of `c >>= fn`,
 * and the transition reads: run `c`, having set *what to do afterwards* aside on the
 * stack.
 *
 * This is defunctionalization proper. The continuation `fn` is neither applied nor kept
 * in a closure of the machine; it is parked as an explicit frame. That is exactly what
 * later allows `find_prompt` to slice the continuation apart and hand one segment of it
 * to a handler clause—an operation that would be impossible if the continuation were an
 * opaque function.
 *)
val step_op
    (#v #cl: Type)
    (apply: apply_t v cl)
    (c: comp_tree v cl)
    (fn: v -> comp_tree v cl)
    (k: stack v cl)
  : Lemma (step apply (Step (Op c fn) k) == Step c (BindF fn :: k))

(**
 * **The Handle transition**: entering `Handle hs ret body` pushes a `PromptF hs ret`
 * frame and continues with `body`. The handler table and the return clause are carried
 * by that frame, so nothing about a handler ever lives outside the stack.
 *
 * The frame is what delimits the handler's scope: whatever the machine pushes while
 * running `body` sits *inside* the scope, and whatever was already there sits outside.
 * All later traffic in prompts keys on this one landmark—`step_perform` locates its
 * handler by scanning for it (`find_prompt`) and cuts the captured segment at it,
 * `step_var_prompt` pops it when a value reaches it, and `Resumed` puts it back on
 * resumption, which is what makes the semantics deep.
 *)
val step_handle
    (#v #cl: Type)
    (apply: apply_t v cl)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma (step apply (Step (Handle hs ret body) k) == Step body (PromptF hs ret :: k))

(**
 * **Reaching a value with an empty stack ends the run**: there is nothing left to do
 * with the value, so the machine halts on `Done`. This is the sole way a `Done` state
 * is ever produced.
 *)
val step_var_done
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
  : Lemma (step apply (Step (Var value) ([] <: stack v cl)) == Done value)

(**
 * **A value meeting a `BindF` frame feeds the saved continuation**: the frame parked by
 * `step_op` is popped and applied to the value. This is the monad law
 * `pure v >>= f == f v`, realized as a single transition of the machine, and it is the
 * counterpart of `step_op`: what one transition sets aside, the other picks back up.
 *)
val step_var_bind
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
    (fn: v -> comp_tree v cl)
    (rest: stack v cl)
  : Lemma (step apply (Step (Var value) (BindF fn :: rest)) == Step (fn value) rest)

(**
 * **A value reaching a prompt leaves the handler's scope**: the handled body ran to
 * completion without ever firing an operation this prompt is responsible for, so the
 * prompt has nothing left to do. It is discarded, and the return clause is applied to
 * the value. With no return clause the transition is the identity on the value: it
 * simply passes through, on the stack the prompt used to sit on.
 *
 * This is the counterpart of `(frame.args.pure ?? Pure)(val)` in the TypeScript runtime.
 *
 * Why this matters to the runtime:
 *   This is the *only* place in the whole of `step` where a return clause is ever
 *   applied, and the prompt carrying it is consumed by the very same transition, so it
 *   cannot be reached a second time through that frame. That is the ground on which the
 *   theorem still ahead—*the return clause runs exactly once, and last*—will rest:
 *   *once*, because the prompt is spent here; *last*, because arriving at this frame
 *   means the handled body, together with everything that had been pushed on top of the
 *   prompt, has already been reduced to a value.
 *)
val step_var_prompt
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

(**
 * **A handler without a return clause is transparent to values**: the `None` case of
 * `step_var_prompt`, singled out. The prompt is dropped and the value carries on
 * unchanged over the remaining stack.
 *
 * Read at the level of types, this says such a handler does not alter the answer type:
 * it may install operations, but it cannot reinterpret the result of the block it
 * delimits.
 *)
val step_var_prompt_identity
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
    (hs: handlers cl)
    (rest: stack v cl)
  : Lemma (step apply (Step (Var value) (PromptF hs None :: rest)) == Step (Var value) rest)

(**
 * **Installing a handler makes its operations handled**: once a `PromptF hs ret` frame
 * has been pushed, every (eff, op) listed in `hs` satisfies `handled_in` on the
 * resulting stack, whatever the frames underneath happen to be.
 *
 * Why this matters to the runtime:
 *   Paired with the contrapositive of `step_perform_stuck`—a stack that handles the
 *   action does not lead to `Stuck`—this yields the statement one actually wants about
 *   `Handle`: *performing, from within the body of a `Handle`, an operation its table
 *   declares can never wedge the machine.* That is the first genuine component of a
 *   *progress* theorem. What is still missing is that the prompt survives while the body
 *   runs, and that is what `handled_in_cons` supplies.
 *)
val handle_installs
    (#v #cl: Type)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (k: stack v cl)
    (eff op: string)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures handled_in eff op (PromptF hs ret :: k))

(**
 * **Monotonicity of `handled_in` under pushing**: a handler already present on the stack
 * is not lost when a further frame is pushed on top of it.
 *
 * Why this matters to the runtime:
 *   The two structural transitions of the machine both work by pushing—`BindF` in
 *   `step_op`, `PromptF` in `step_handle`. This lemma says neither of them can break a
 *   scope: descending into the left-hand side of a bind, or into the body of an inner
 *   `Handle`, never takes an outer handler out of reach. Together with `handle_installs`
 *   it is what carries *the handler is still in place* along a run, and that is precisely
 *   the induction step a progress theorem needs.
 *)
val handled_in_cons
    (#v #cl: Type)
    (eff op: string)
    (f: frame v cl)
    (k: stack v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures handled_in eff op (f :: k))

//------------------------//

(**
 * **Terminal states are fixpoints**: once the machine has reached `Done` or `Stuck`,
 * running it for any further number of transitions changes nothing.
 *
 * This is the multi-step counterpart of the two absorbing branches of `step`, and it is
 * what makes `fuel` semantically inert: an answer obtained with a given amount of fuel is
 * not disturbed by feeding in more.
 *
 * Its immediate use is proof-technical. Every induction over the length of a run splits
 * on the shape of the current state, and this lemma is what discharges the terminal
 * branches—`steps_add` is proved exactly this way. Without it the two sides of an
 * interval decomposition cannot be shown to agree once the machine has already halted
 * inside the first interval.
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
 * **Additivity of multi-step execution**: running for `n` transitions and then for `m`
 * more is running for `n + m` transitions. Equivalently, a run may be cut at any point
 * and the two halves reasoned about separately.
 *
 * This is the pivotal lemma of this group: it is the glue with which a property spanning
 * several transitions is assembled out of properties of shorter stretches. Without it,
 * multi-step statements cannot even be *phrased* compositionally—one would be forced to
 * unfold a fixed number of transitions by hand, which is impossible as soon as the length
 * of a stretch is not known in advance.
 *
 * Why this matters to the runtime:
 *   `step_perform` and `capture_resume_roundtrip` currently sit side by side as two
 *   isolated single-transition facts. To fuse them into the single proposition one
 *   actually wants—*performing an operation and coming back into the continuation takes
 *   N transitions, and lands on the original stack*—one has to account for what happens
 *   in between, namely the execution of the clause body returned by `apply`. That body is
 *   an arbitrary computation of unknown length. The run therefore has to be split into
 *   *one transition (the perform) + j transitions (the clause body) + one transition (the
 *   resume)*, and it is this lemma that welds the three intervals back together.
 *
 * The same shape is needed for the theorems still ahead: that a handler's return clause
 * is applied exactly once and at the very end; that a `Handle` node's prompt survives
 * from its installation until its removal; and, eventually, an adequacy theorem relating
 * the machine to a denotational semantics, whose proof is an induction that repeatedly
 * concatenates sub-runs.
 *)
val steps_add
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n m: nat)
    (s: state v cl)
  : Lemma
      (ensures steps apply (n + m) s == steps apply m (steps apply n s))

(**
 * **Stability of the answer**: once a run has produced a `Done`, adding fuel never
 * changes it. A corollary of `steps_add` and `steps_terminal`.
 *
 * The point is that the result of the machine does not depend on how much fuel it was
 * given, as long as it was given enough. This is what justifies the habit—in the tests
 * and in specifications alike—of passing a comfortably large constant and reading off the
 * result: the value observed is the value the machine converges to, not an artifact of
 * the bound. It also means a specification may quantify existentially over the fuel
 * (*there is some n for which the machine is `Done`*) without the choice of witness
 * mattering.
 *)
val steps_stable
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n m: nat)
    (s: state v cl)
  : Lemma
      (requires Done? (steps apply n s))
      (ensures steps apply (n + m) s == steps apply n s)
