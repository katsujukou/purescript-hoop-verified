(**
 * **The runtime that ships**: the evidence-passing machine `<C, E, K>`, with
 * tail-resumptive ("fast") handler clauses, linked to the reference machine by a
 * WEAK SIMULATION rather than by per-transition state equality.
 *
 * C and K are `Hoop.Runtime.Syntax`; the reference reading of the transitions is
 * `Hoop.Runtime.Semantics`. This module supplies E. In a conventional CEK
 * machine E maps variables to values; in Hoop, lexical environments are already
 * captured by PureScript/JavaScript closures, so E is repurposed as an *evidence
 * environment* mapping each handled operation to the prompt that handles it and
 * to the environment outside that prompt. `Hoop.Runtime.Semantics.step` searches
 * the stack at every `perform`; here that search is one `Env.lookup`.
 *
 * Three layers, and the middle one is the machine:
 *
 *   1. `Hoop.Runtime.Semantics`, untouched, instantiated at the clause type
 *      `clause cl`. It knows nothing about `fast`: the reference reading of a
 *      fast clause is *constructed here*, by `desugar`, as the ordinary ctl
 *      clause `fun args k -> Op (apply_fast c args) k`. No new frame
 *      constructor, no mask, no change to `handled_in` or `find_prompt`.
 *
 *   2. The machine. `mstate` carries the evidence environment in its
 *      configuration and has an `MEnvF` frame that exists only on this side. A
 *      fast clause body runs *in place* -- nothing is captured, the stack is not
 *      cut -- under the handler's own environment, with the perform site's
 *      environment saved in the frame.
 *
 *   3. The link. `erase_st` maps a machine configuration to a reference
 *      state, and `msim` says one machine transition is one *or two* reference
 *      transitions. Never zero, so there is no stuttering to rank.
 *
 * `execute` is the extracted entry point -- what `runtime/ml/hoop_ffi.ml` calls,
 * and the only thing in the development that touches the FFI boundary. Its
 * postcondition is stated about `Hoop.Runtime.Semantics.steps` through
 * `erase_st`, so `Hoop.Runtime.Metatheory` and `Hoop.Runtime.Laws` continue to
 * speak about the reference machine without a line being restated: specification
 * and implementation, in that order.
 *
 * *Why a weak simulation and not state equality.* An earlier machine kept the
 * environment beside a reference `state` and proved the two agree transition by
 * transition. That is unavailable here by construction: a fast clause body runs
 * without the capture the reference performs, so the two stacks stop having the
 * same length -- an `MEnvF` stands for a whole segment of the reference stack.
 * `erase_st` is what relates them, and `msim` is the equality that survives.
 *
 * *Why no height is tracked.* Locating a prompt by the height it was installed
 * at is an index into the *reference* stack, which `MEnvF` makes unavailable.
 * `msplit` below therefore walks -- and walks only the captured part, which is
 * the property evidence passing exists to buy, and the one a height was only
 * ever a means to. The module consequently keeps its own `env_of_stack`, at a
 * payload that is a prompt frame and nothing else.
 *)
module Hoop.Runtime

open FStar.List.Tot
open Hoop.Runtime.Syntax
open Hoop.Runtime.Semantics

module E = Hoop.Runtime.Env
module MT = Hoop.Runtime.Metatheory

(* ------------------------------------------------------------------ *)
(*  1.  Clauses: the fast/full distinction, visible to F*              *)
(* ------------------------------------------------------------------ *)

(**
 * **A clause, tagged.** The FFI hands over an opaque handle `cl` together with
 * *two* interpreters (`full_t`, `fast_t`); which one applies is decided by this
 * tag, which F* can see. The equivalence `fast f == ctl (\args k -> bind (f
 * args) k)` is therefore a definition -- `desugar` -- rather than an assumption
 * at the boundary.
 *)
noeq
type clause (cl: Type u#a) : Type u#a =
  | Full : c:cl -> clause cl
  | Fast : c:cl -> clause cl

let ct (v: Type) (cl: Type) = comp_tree v (clause cl)
let rframe (v cl: Type) = frame v (clause cl)
let rstack (v cl: Type) = stack v (clause cl)
let rstate (v cl: Type) = state v (clause cl)

(** **The two FFI interpreters.** A full clause is handed the delimited
    continuation; a fast clause is not, and cannot be. *)
let full_t (v cl: Type) = cl -> list v -> (v -> ct v cl) -> ct v cl
let fast_t (v cl: Type) = cl -> list v -> ct v cl

(**
 * **The desugaring**, i.e. the reference reading of a tagged clause. This is the
 * `apply` the reference machine is run with. A `Fast c` clause reads as the ctl
 * clause that binds the body to the continuation and resumes exactly once --
 * built here, in F*, not trusted from outside.
 *
 * `noextract`: the machine never dispatches through this. It calls
 * `af` and `afast` directly, which is what makes the tag free at run time.
 *)
noextract
let desugar (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
  : apply_t v (clause cl)
  = fun c payload k ->
      match c with
      | Full c0 -> af c0 payload k
      | Fast c0 -> Op (afast c0 payload) k

(* ------------------------------------------------------------------ *)
(*  2.  The machine                                          *)
(* ------------------------------------------------------------------ *)

(**
 * **What a level of the evidence environment carries here**: the prompt frame
 * and nothing else. No height, no prompt count -- the machine never
 * needs to locate a prompt by arithmetic, because it never cuts its stack at one
 * except through `msplit`, which walks.
 *)
let pd (v cl: Type) = f: rframe v cl { PromptF? f }
let menv (v cl: Type) = E.env (pd v cl)

(**
 * **The environment a *reference* stack offers.** One level per prompt,
 * innermost first. The machine's environment is compared against this,
 * up to `E.equiv`, in `config_ok`.
 *
 * `noextract`: it states an invariant, and no transition computes it -- the
 * machine carries its environment rather than rebuilding it.
 *)
noextract
let rec env_of_stack (#v #cl: Type) (k: rstack v cl)
  : Tot (menv v cl) (decreases k)
  = match k with
    | [] -> E.empty
    | BindF _ :: r -> env_of_stack r
    | PromptF hs ret :: r ->
        E.extend (env_of_stack r) (keys hs) (PromptF hs ret <: pd v cl)

(**
 * **The machine frames.** `MEnvF` is the one that has no counterpart in the
 * reference machine: it marks a tail-resumptive clause body running in place. It
 * carries the operation whose clause is running -- which is how its own prompt
 * is re-found -- and the environment in force at the perform site, which is
 * restored when the body completes. No height, no count.
 *)
noeq
type mframe (v cl: Type) =
  | MBindF : fn:(v -> ct v cl) -> mframe v cl
  | MPromptF : hs:handlers (clause cl) -> ret:option (v -> ct v cl) -> mframe v cl
  | MEnvF : eff:string -> op:string -> saved:menv v cl -> mframe v cl

let mstack (v cl: Type) = list (mframe v cl)

(** **The machine state.** `MStep` carries the environment; the
    reference `state` does not, and does not need to. *)
noeq
type mstate (v cl: Type) =
  | MDone : value:v -> mstate v cl
  | MStep : c:ct v cl -> w:menv v cl -> k:mstack v cl -> mstate v cl
  | MStuck : eff:string -> op:string -> mstate v cl

(* ------------------------------------------------------------------ *)
(*  3.  The erasure                                                    *)
(* ------------------------------------------------------------------ *)

(**
 * **The erasure of a machine stack to a reference stack.**
 *
 * `MBindF` and `MPromptF` map across unchanged. An `MEnvF` erases to the frame
 * the reference machine really has at that point: the desugared fast clause
 * pushed `BindF (kont_of captured)` -- the continuation of the ctl clause it
 * desugars to -- and the frames from the `MEnvF` down to and including its own
 * prompt are exactly that captured segment, so they are *absorbed*.
 *
 * The erasure is therefore partial: it is defined only when the `MEnvF`'s prompt
 * really is below it. That is the definedness condition of `erase_k`, and
 * `stack_ok` is the invariant which supplies it. It lives on this side only; the
 * reference machine never hears of it.
 *
 * The continuation is written `Hoop.Runtime.Semantics.kont_of captured`, which
 * is how `Hoop.Runtime.Semantics.step` writes it too, so the two are the same
 * term rather than two anonymous closures that happen to elaborate alike.
 *)
let rec erase_k (#v #cl: Type) (kk: mstack v cl)
  : GTot (option (rstack v cl)) (decreases kk)
  = match kk with
    | [] -> Some []
    | MBindF fn :: r ->
        (match erase_k r with None -> None | Some k -> Some (BindF fn :: k))
    | MPromptF hs ret :: r ->
        (match erase_k r with None -> None | Some k -> Some (PromptF hs ret :: k))
    | MEnvF eff op _ :: r ->
        (match erase_k r with
          | None -> None
          | Some k ->
            (match find_prompt eff op k with
              | None -> None
              | Some (captured, clause, below) ->
                  Some (BindF (kont_of captured) :: below)))

let erase_st (#v #cl: Type) (q: mstate v cl) : GTot (option (rstate v cl)) =
  match q with
  | MDone x -> Some (Done x)
  | MStuck e o -> Some (Stuck e o)
  | MStep c w kk -> (match erase_k kk with None -> None | Some k -> Some (Step c k))

(* ------------------------------------------------------------------ *)
(*  4.  The invariant                                                  *)
(* ------------------------------------------------------------------ *)

(**
 * **The machine stack is well formed.** Two things, at every `MEnvF`:
 *
 *   - its prompt is below it and *inside the same erased stack*
 *     (`handled_in`), which is what makes `erase_k` total here;
 *   - the environment it saved is the environment the frames below it offer,
 *     which is what makes restoring it on completion correct.
 *
 * Confined to this module. Nothing in `Hoop.Runtime.Semantics` mentions it.
 *)
let rec stack_ok (#v #cl: Type) (kk: mstack v cl) : GTot prop (decreases kk) =
  match kk with
  | [] -> True
  | MBindF _ :: r -> stack_ok r
  | MPromptF _ _ :: r -> stack_ok r
  | MEnvF eff op saved :: r ->
      stack_ok r /\
      (match erase_k r with
        | None -> False
        | Some k -> handled_in eff op k /\ saved `E.equiv` env_of_stack k)

(** **The machine invariant.** The stack is well formed and the environment is
    the one the *erased* stack offers -- which, when an `MEnvF` is in flight, is
    the fast clause's own `below`, since the erasure absorbed the frames down to
    its prompt. *)
let config_ok (#v #cl: Type) (q: mstate v cl) : GTot prop =
  match q with
  | MDone _ -> True
  | MStuck _ _ -> True
  | MStep _ w kk ->
      stack_ok kk /\
      (match erase_k kk with
        | None -> False
        | Some k -> w `E.equiv` env_of_stack k)

(* ------------------------------------------------------------------ *)
(*  5.  The machine transition                                       *)
(* ------------------------------------------------------------------ *)

(**
 * **Splitting the machine stack at the prompt handling `(eff, op)`**, in one
 * pass: it returns *both* the segment the clause is to be handed -- already in
 * reference frames, which is the form a delimited continuation travels in -- and
 * the machine stack the machine runs on below the prompt.
 *
 * The erasure is fused into the walk rather than run before it. Only the
 * captured part is visited; the frames below the handling prompt are handed back
 * untouched. This is what evidence passing exists to make possible.
 *
 * The one place where an `MEnvF` needs care: while a fast clause body is in
 * flight, the prompts between the `MEnvF` and its own prompt are *masked* --
 * they are not in the environment, and the erasure absorbs them -- so the search
 * must jump over them wholesale. It does so by re-running itself on the
 * `MEnvF`'s own key. The segment that jump skips is exactly what the erasure
 * absorbs into a single `BindF (kont_of ...)`, and that frame is what goes into
 * the captured segment here, so the two agree by construction rather than by a
 * later argument -- see `msplit_agrees`.
 *
 * The refinement makes the remaining stack a strict suffix, which is what
 * discharges termination of the two-phase `MEnvF` branch.
 *
 * *This is the specification.* What the machine runs is `msplit_fast` below,
 * which computes the same answer without a recursion as deep as the segment is
 * long; see there.
 *)
noextract
let rec msplit (#v #cl: Type) (eff op: string) (kk: mstack v cl)
  : Tot (o: option (rstack v cl & mstack v cl)
          { match o with None -> True | Some (_, b) -> length b < length kk })
        (decreases (length kk))
  = match kk with
    | [] -> None
    | MBindF fn :: r ->
        (match msplit eff op r with
          | None -> None
          | Some (cap, b) -> Some (BindF fn :: cap, b))
    | MPromptF hs ret :: r ->
        (match lookup_clause hs eff op with
          | Some _ -> Some ([PromptF hs ret], r)
          | None ->
            (match msplit eff op r with
              | None -> None
              | Some (cap, b) -> Some (PromptF hs ret :: cap, b)))
    | MEnvF e' o' _ :: r ->
        (match msplit e' o' r with
          | None -> None
          | Some (cap', mrest) ->
            (match msplit eff op mrest with
              | None -> None
              | Some (cap, b) -> Some (BindF (kont_of cap') :: cap, b)))

(** **Leaving a prompt**: pop one level. The guard is unreachable under
    `config_ok` and is written out so that `mstep` is a total function. *)
let pop_env (#v #cl: Type) (w: menv v cl) : Tot (menv v cl) =
  if E.is_empty w then w else E.outer w

(**
 * **Splicing a captured segment back on.** A captured segment is made of
 * *reference* frames -- it travels inside a `Resumed` node of the shared AST --
 * so resuming injects them back as machine frames. No `MEnvF` can appear in
 * one: the erasure turned every `MEnvF` into a `BindF` when the segment was
 * captured.
 *
 * The specification; `inj_append` below is what runs.
 *)
noextract
let rec inj_k (#v #cl: Type) (k: rstack v cl) : Tot (mstack v cl) (decreases k) =
  match k with
  | [] -> []
  | BindF fn :: r -> MBindF fn :: inj_k r
  | PromptF hs ret :: r -> MPromptF hs ret :: inj_k r

(**
 * **Re-deriving the environment of a spliced segment**, against the environment
 * in force *now*: a segment may be resumed under a stack other than the one it
 * was captured on, so nothing captured with it may be reused.
 *
 * The specification; `mreinstall_fast` below is what runs.
 *)
noextract
let rec mreinstall (#v #cl: Type) (w: menv v cl) (k: rstack v cl)
  : Tot (menv v cl) (decreases k)
  = match k with
    | [] -> w
    | BindF _ :: r -> mreinstall w r
    | PromptF hs ret :: r ->
        E.extend (mreinstall w r) (keys hs) (PromptF hs ret <: pd v cl)

(* ------------------------------------------------------------------ *)
(*  5a.  The three walks, as loops                                     *)
(*                                                                     *)
(*  `inj_k`, `mreinstall` and `msplit` are all structurally recursive   *)
(*  over a captured segment, and the extracted runtime maps that depth  *)
(*  onto the host's call stack -- a few tens of thousands of frames     *)
(*  that are the user's to spend, not the machine's. Each is therefore  *)
(*  paired with an accumulating loop, proved equal to it, and the       *)
(*  equality lives in the loop's type so that every statement about the *)
(*  specification is a statement about what runs.                       *)
(* ------------------------------------------------------------------ *)

(* Injection, as a fold from the bottom of the segment. *)
let rec inj_onto (#v #cl: Type) (rk: rstack v cl) (acc: mstack v cl)
  : Tot (mstack v cl) (decreases rk)
  = match rk with
    | [] -> acc
    | BindF fn :: r -> inj_onto r (MBindF fn :: acc)
    | PromptF hs ret :: r -> inj_onto r (MPromptF hs ret :: acc)

private
let rec inj_onto_append (#v #cl: Type) (l1 l2: rstack v cl) (acc: mstack v cl)
  : Lemma (ensures inj_onto (l1 @ l2) acc == inj_onto l2 (inj_onto l1 acc)) (decreases l1)
  = match l1 with
    | [] -> ()
    | BindF fn :: r -> inj_onto_append r l2 (MBindF fn :: acc)
    | PromptF hs ret :: r -> inj_onto_append r l2 (MPromptF hs ret :: acc)

private
let rec inj_onto_rev (#v #cl: Type) (k: rstack v cl) (acc: mstack v cl)
  : Lemma (ensures inj_onto (rev k) acc == inj_k k @ acc) (decreases k)
  = match k with
    | [] -> ()
    | f :: r ->
        inj_onto_rev r acc;
        rev_rev' k;
        rev_rev' r;
        inj_onto_append (rev r) [f] acc

(** **Splicing, without recursing over the segment.** *)
let inj_append (#v #cl: Type) (k: rstack v cl) (kk: mstack v cl)
  : Tot (o: mstack v cl { o == inj_k k @ kk })
  = inj_onto_rev k kk;
    inj_onto (rev k) kk

(* Re-derivation, as a fold from the bottom of the segment. *)
let rec mreinstall_loop (#v #cl: Type) (w: menv v cl) (rk: rstack v cl)
  : Tot (menv v cl) (decreases rk)
  = match rk with
    | [] -> w
    | BindF _ :: r -> mreinstall_loop w r
    | PromptF hs ret :: r ->
        mreinstall_loop (E.extend w (keys hs) (PromptF hs ret <: pd v cl)) r

private
let rec mreinstall_loop_append (#v #cl: Type) (w: menv v cl) (l1 l2: rstack v cl)
  : Lemma
      (ensures mreinstall_loop w (l1 @ l2) == mreinstall_loop (mreinstall_loop w l1) l2)
      (decreases l1)
  = match l1 with
    | [] -> ()
    | BindF _ :: r -> mreinstall_loop_append w r l2
    | PromptF hs ret :: r ->
        mreinstall_loop_append (E.extend w (keys hs) (PromptF hs ret <: pd v cl)) r l2

private
let rec mreinstall_loop_rev (#v #cl: Type) (w: menv v cl) (k: rstack v cl)
  : Lemma (ensures mreinstall_loop w (rev k) == mreinstall w k) (decreases k)
  = match k with
    | [] -> ()
    | f :: r ->
        mreinstall_loop_rev w r;
        rev_rev' k;
        rev_rev' r;
        mreinstall_loop_append w (rev r) [f]

(** **Re-deriving, without recursing over the segment.** *)
let mreinstall_fast (#v #cl: Type) (w: menv v cl) (k: rstack v cl)
  : Tot (w': menv v cl { w' == mreinstall w k })
  = mreinstall_loop_rev w k;
    mreinstall_loop w (rev k)

(**
 * **The split, without recursing over the captured segment.** `acc` holds the
 * frames captured so far, innermost last, so the answer is `rev acc` -- the same
 * reversal trick the two loops above use, and `rev` is itself a loop in
 * `runtime/ml/shim/FStar_List_Tot_Base.ml`.
 *
 * The nested call in the `MEnvF` branch is genuinely nested and not a tail call.
 * It cannot be otherwise: jumping over a masked region means finding its far end
 * first. Its depth is the number of *nested fast clause bodies* in flight inside
 * the captured segment, not the number of frames -- and a fast clause body that
 * performs another fast operation is the only way to nest one.
 *)
let rec msplit_acc (#v #cl: Type) (eff op: string) (acc: rstack v cl) (kk: mstack v cl)
  : Tot (o: option (rstack v cl & mstack v cl)
          { match o with None -> True | Some (_, b) -> length b < length kk })
        (decreases (length kk))
  = match kk with
    | [] -> None
    | MBindF fn :: r -> msplit_acc eff op (BindF fn :: acc) r
    | MPromptF hs ret :: r ->
        (match lookup_clause hs eff op with
          | Some _ -> Some (rev (PromptF hs ret :: acc), r)
          | None -> msplit_acc eff op (PromptF hs ret :: acc) r)
    | MEnvF e' o' _ :: r ->
        (match msplit_acc e' o' [] r with
          | None -> None
          | Some (cap', mrest) -> msplit_acc eff op (BindF (kont_of cap') :: acc) mrest)

(* What the accumulating walk computes, in terms of the specification: the same
   answer, with whatever was already accumulated in front of the captured
   segment. Named so that no `match` appears in the statement of a lemma. *)
private
let msplit_acc_ok
    (#v #cl: Type) (eff op: string) (acc: rstack v cl) (kk: mstack v cl)
  : GTot prop
  = match msplit_acc eff op acc kk, msplit eff op kk with
    | None, None -> True
    | Some (cap1, b1), Some (cap2, b2) -> cap1 == rev acc @ cap2 /\ b1 == b2
    | _ -> False

(* Pushing one frame onto the accumulator prepends it to the captured segment.
   The only arithmetic of `rev` the proof needs, and it is stated here so that
   the induction below cites it rather than re-derives it three times. *)
private
let rev_cons_append (#a: Type) (x: a) (acc l: list a)
  : Lemma (rev (x :: acc) @ l == rev acc @ (x :: l))
  = rev_rev' (x :: acc);
    rev_rev' acc;
    append_assoc (rev acc) [x] l

private
let rec msplit_acc_agrees
    (#v #cl: Type) (eff op: string) (acc: rstack v cl) (kk: mstack v cl)
  : Lemma (ensures msplit_acc_ok eff op acc kk) (decreases (length kk))
  = match kk with
    | [] -> ()
    | MBindF fn :: r ->
        msplit_acc_agrees eff op (BindF fn :: acc) r;
        (match msplit eff op r with
          | None -> ()
          | Some (cap, _) -> rev_cons_append (BindF fn <: rframe v cl) acc cap)
    | MPromptF hs ret :: r ->
        (match lookup_clause hs eff op with
          | Some _ ->
              rev_cons_append (PromptF hs ret <: rframe v cl) acc [];
              append_l_nil (rev (PromptF hs ret :: acc));
              append_l_nil (rev acc)
          | None ->
              msplit_acc_agrees eff op (PromptF hs ret :: acc) r;
              (match msplit eff op r with
                | None -> ()
                | Some (cap, _) -> rev_cons_append (PromptF hs ret <: rframe v cl) acc cap))
    | MEnvF e' o' _ :: r ->
        msplit_acc_agrees e' o' [] r;
        (match msplit e' o' r with
          | None -> ()
          | Some (cap', mrest) ->
            msplit_acc_agrees eff op (BindF (kont_of cap') :: acc) mrest;
            (match msplit eff op mrest with
              | None -> ()
              | Some (cap, _) -> rev_cons_append (BindF (kont_of cap') <: rframe v cl) acc cap))

(** **The split the machine runs.** Its answer is the specification's, and the
    equality is in the type, so `msplit_agrees` below speaks about both at once. *)
let msplit_fast (#v #cl: Type) (eff op: string) (kk: mstack v cl)
  : Tot (o: option (rstack v cl & mstack v cl) { o == msplit eff op kk })
  = msplit_acc_agrees eff op [] kk;
    msplit_acc eff op [] kk

(**
 * **One transition of the machine.**
 *
 *   - `Op`, `Handle`, `Var`  behave as in `Hoop.Runtime`.
 *   - `Var` over an `MEnvF`  is the *return* from a tail-resumptive body: the
 *                            perform site's environment comes back and the value
 *                            flows on as the operation's result. Nothing is
 *                            spliced -- the frames are still on the stack.
 *   - `Perform` / `Fast`     runs the body in place, under the handler's own
 *                            environment (`ev.below`), with an `MEnvF` marking
 *                            the boundary. The continuation is NOT captured and
 *                            the stack is NOT cut.
 *   - `Perform` / `Full`     the existing path: capture, hand the segment to the
 *                            clause, run on below the prompt.
 *   - `Resumed`              splice and re-derive.
 *
 * *What a capture does to an `MEnvF`.* A delimited continuation travels inside a
 * `Resumed` node of the *shared* AST, so it is made of reference frames; the
 * captured segment handed to a full clause is therefore the *erasure* of the
 * machine segment, with each `MEnvF` in it replaced by the `BindF` the
 * reference machine has there. Resuming splices reference frames back
 * (`inj_append`), so no `MEnvF` is ever reinstalled: the tail-resumptive
 * optimisation lapses for a body that has been captured, and the machine behaves
 * exactly as the reference from that point. This is deliberate. It keeps a
 * single AST, avoids an FFI naturality assumption, and makes multi-shot
 * resumption automatically safe.
 *
 * *The `Full` branch does what a shipping implementation would do.* It calls the
 * split once, which walks the captured part of the stack and no further, and it
 * invokes the FFI's full interpreter `af` directly -- there is no dispatch
 * through `desugar` to be optimised away later.
 *)
let mstep
    (#v #cl: Type)
    (af: full_t v cl)
    (afast: fast_t v cl)
    (q: mstate v cl)
  : Tot (mstate v cl)
  = match q with
    | MDone _ -> q
    | MStuck _ _ -> q
    | MStep c w kk ->
      match c with
      | Op comp fn -> MStep comp w (MBindF fn :: kk)
      | Handle hs ret body ->
          MStep body (E.extend w (keys hs) (PromptF hs ret <: pd v cl)) (MPromptF hs ret :: kk)
      | Var value ->
          (match kk with
            | [] -> MDone value
            | MBindF fn :: r -> MStep (fn value) w r
            | MPromptF hs ret :: r ->
                let w' = pop_env w in
                (match ret with
                  | Some fn -> MStep (fn value) w' r
                  | None -> MStep (Var value) w' r)
            | MEnvF _ _ saved :: r -> MStep (Var value) saved r)
      | Perform eff op payload ->
          (match E.lookup w (eff, op) with
            | None -> MStuck eff op
            | Some ev ->
              (match lookup_clause (PromptF?.hs ev.E.prompt) eff op with
                | None -> MStuck eff op
                | Some (Fast c0) ->
                    MStep (afast c0 payload) ev.E.below (MEnvF eff op w :: kk)
                | Some (Full c0) ->
                  (match msplit_fast eff op kk with
                    | None -> MStuck eff op
                    | Some (captured, b) ->
                        MStep (af c0 payload (kont_of captured)) ev.E.below b)))
      | Resumed kont value ->
          MStep (Var value) (mreinstall_fast w kont) (inj_append kont kk)

(* ------------------------------------------------------------------ *)
(*  6.  Reference-side facts about `find_prompt`                        *)
(*                                                                     *)
(*  `find_prompt` recurses structurally, so its two equations -- skip a *)
(*  frame that does not handle, stop at a matching `PromptF` -- hold by  *)
(*  unfolding, captured segment included. That is what the fused         *)
(*  `msplit` needs: it builds the captured segment as it walks, so       *)
(*  agreeing with `find_prompt` means agreeing on all three components.  *)
(* ------------------------------------------------------------------ *)

let fp_same (#v #cl: Type) (o1 o2: option (stack v cl & cl & stack v cl)) : prop =
  match o1, o2 with
  | None, None -> True
  | Some (_, c1, b1), Some (_, c2, b2) -> c1 == c2 /\ b1 == b2
  | _ -> False

(** **A bind frame is transparent to the search.** *)
let fp_bind (#v #cl: Type) (eff op: string) (fn: v -> comp_tree v cl) (k: stack v cl)
  : Lemma (fp_same (find_prompt eff op (BindF fn :: k)) (find_prompt eff op k))
  = ()

(** **A prompt that handles the action stops the search there.** *)
let fp_prompt_hit
    (#v #cl: Type) (eff op: string)
    (hs: handlers cl) (ret: option (v -> comp_tree v cl)) (k: stack v cl)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures
        find_prompt eff op (PromptF hs ret :: k)
          == Some ([PromptF hs ret], Some?.v (lookup_clause hs eff op), k))
  = ()

(** **A prompt that does not is transparent too.** *)
let fp_prompt_miss
    (#v #cl: Type) (eff op: string)
    (hs: handlers cl) (ret: option (v -> comp_tree v cl)) (k: stack v cl)
  : Lemma
      (requires None? (lookup_clause hs eff op))
      (ensures fp_same (find_prompt eff op (PromptF hs ret :: k)) (find_prompt eff op k))
  = ()

(* ------------------------------------------------------------------ *)
(*  7.  Environment / stack correspondence                             *)
(* ------------------------------------------------------------------ *)

(** **Extending respects `equiv`.** *)
let extend_equiv (#v #cl: Type) (w1 w2: menv v cl) (ks: keyset) (x: pd v cl)
  : Lemma (requires w1 `E.equiv` w2) (ensures E.extend w1 ks x `E.equiv` E.extend w2 ks x)
  = ()

(** **Popping a prompt pops exactly one level.** *)
let pop_env_agrees
    (#v #cl: Type) (w: menv v cl)
    (hs: handlers (clause cl)) (ret: option (v -> ct v cl)) (k: rstack v cl)
  : Lemma
      (requires w `E.equiv` env_of_stack (PromptF hs ret :: k))
      (ensures pop_env w `E.equiv` env_of_stack k)
  = let lvl : E.level (pd v cl) =
      { E.keys = keyset_view (keys hs); E.payload = (PromptF hs ret <: pd v cl) } in
    assert (env_of_stack (PromptF hs ret :: k)
            == E.extend (env_of_stack k) (keys hs) (PromptF hs ret <: pd v cl));
    assert (E.levels (env_of_stack (PromptF hs ret :: k))
            == lvl :: E.levels (env_of_stack k));
    assert (E.levels w == lvl :: E.levels (env_of_stack k));
    assert (E.depth w == length (E.levels w));
    assert (E.depth w > 0)

(** **Splicing a segment on and re-deriving from the bottom agree.** *)
let rec mreinstall_agrees (#v #cl: Type) (k1 k2: rstack v cl)
  : Lemma (ensures env_of_stack (k1 @ k2) == mreinstall (env_of_stack k2) k1) (decreases k1)
  = match k1 with
    | [] -> ()
    | _ :: r -> mreinstall_agrees r k2

(** **Re-deriving respects `equiv`**, so the machine may reinstall onto its own
    environment rather than onto one rebuilt from the stack. *)
let rec mreinstall_equiv (#v #cl: Type) (w1 w2: menv v cl) (k: rstack v cl)
  : Lemma (requires w1 `E.equiv` w2)
          (ensures mreinstall w1 k `E.equiv` mreinstall w2 k)
          (decreases k)
  = match k with
    | [] -> ()
    | _ :: r -> mreinstall_equiv w1 w2 r

(* ------------------------------------------------------------------ *)
(*  8.  The erasure and splicing                                       *)
(* ------------------------------------------------------------------ *)

(** **Injected reference frames erase back to themselves**, and the erasure
    distributes over the splice. *)
let rec erase_inj_append (#v #cl: Type) (k1: rstack v cl) (kk: mstack v cl)
  : Lemma
      (ensures
        (match erase_k kk with
          | None -> erase_k (inj_k k1 @ kk) == None
          | Some k -> erase_k (inj_k k1 @ kk) == Some (k1 @ k)))
      (decreases k1)
  = match k1 with
    | [] -> ()
    | _ :: r -> erase_inj_append r kk

(** **Splicing preserves the invariant**: injected frames are never `MEnvF`, so
    they carry no obligation of their own, and the frames below are untouched. *)
let rec stack_ok_inj_append (#v #cl: Type) (k1: rstack v cl) (kk: mstack v cl)
  : Lemma (requires stack_ok kk) (ensures stack_ok (inj_k k1 @ kk)) (decreases k1)
  = match k1 with
    | [] -> ()
    | _ :: r -> stack_ok_inj_append r kk

(* ------------------------------------------------------------------ *)
(*  9.  Dispatch: evidence answers what the stack walk answers          *)
(* ------------------------------------------------------------------ *)

(** **What a lookup in `env_of_stack k` must agree with**: the clause and the
    context `find_prompt` finds on `k`. Named so that no `match` appears in the
    statement of a lemma. *)
let lookup_find_ok (#v #cl: Type) (eff op: string) (k: rstack v cl) : GTot prop =
  match E.lookup (env_of_stack k) (eff, op), find_prompt eff op k with
  | None, None -> True
  | Some ev, Some (cap, c, below) ->
      lookup_clause (PromptF?.hs ev.E.prompt) eff op == Some c /\
      ev.E.below `E.equiv` env_of_stack below
  | _ -> False

let rec lookup_find (#v #cl: Type) (eff op: string) (k: rstack v cl)
  : Lemma (ensures lookup_find_ok eff op k) (decreases k)
  = match k with
    | [] -> E.lookup_empty #(pd v cl) (eff, op)
    | BindF fn :: r ->
        lookup_find eff op r;
        fp_bind eff op fn r
    | PromptF hs ret :: r ->
        let w = env_of_stack r in
        keys_correct hs eff op;
        (match lookup_clause hs eff op with
          | Some _ ->
              E.lookup_extend_hit w (keys hs) (PromptF hs ret <: pd v cl) (eff, op);
              fp_prompt_hit eff op hs ret r
          | None ->
              E.lookup_extend_miss w (keys hs) (PromptF hs ret <: pd v cl) (eff, op);
              lookup_find eff op r;
              fp_prompt_miss eff op hs ret r)

(* ------------------------------------------------------------------ *)
(*  10.  The machine split is the reference split                     *)
(* ------------------------------------------------------------------ *)

(**
 * **What the fused split must agree with**: all three components of
 * `find_prompt` on the erased stack. The captured segment is part of the claim
 * -- `msplit` produces it rather than reading it off an erasure -- and it is
 * claimed to be *equal*, not merely pointwise equal, so the clause this
 * machine invokes and the clause the reference machine invokes are literally the
 * same term.
 *)
let msplit_ok (#v #cl: Type) (eff op: string) (kk: mstack v cl) (k: rstack v cl) : GTot prop =
  match msplit eff op kk, find_prompt eff op k with
  | None, None -> True
  | Some (cap, b), Some (cap', _, below) ->
      cap == cap' /\ stack_ok b /\ erase_k b == Some below
  | _ -> False

(**
 * **The central structural lemma.** Walking the machine stack -- jumping over
 * the region an `MEnvF` masks -- captures the erasure of what `find_prompt`
 * captures and lands on the erasure of what it lands on. This is where the
 * invariant "the `MEnvF`'s prompt sits below it inside the same segment" is
 * spent: without it `erase_k r` would be `None` and the masked region would have
 * no boundary to jump to.
 *)
let rec msplit_agrees (#v #cl: Type) (eff op: string) (kk: mstack v cl) (k: rstack v cl)
  : Lemma
      (requires stack_ok kk /\ erase_k kk == Some k)
      (ensures msplit_ok eff op kk k)
      (decreases (length kk))
  = match kk with
    | [] -> ()
    | MBindF fn :: r ->
        let Some kr = erase_k r in
        msplit_agrees eff op r kr
    | MPromptF hs ret :: r ->
        let Some kr = erase_k r in
        (match lookup_clause hs eff op with
          | Some _ -> fp_prompt_hit eff op hs ret kr
          | None -> msplit_agrees eff op r kr)
    | MEnvF e' o' sv :: r ->
        let Some kr = erase_k r in
        msplit_agrees e' o' r kr;
        (match msplit e' o' r with
          | None -> ()
          | Some (cap', mrest) ->
            let Some (cap'', _, mrest_r) = find_prompt e' o' kr in
            assert (cap' == cap'');
            assert (erase_k mrest == Some mrest_r);
            assert (k == BindF (kont_of cap') :: mrest_r);
            msplit_agrees eff op mrest mrest_r)

(* ------------------------------------------------------------------ *)
(*  11.  What the reference machine does in two steps                   *)
(*                                                                     *)
(*  The two places where one machine transition is two reference      *)
(*  transitions. Both are consequences of the desugaring: a fast        *)
(*  clause reads as `Op (body args) k`, so the reference has to build    *)
(*  the `Op` node and then push its bind frame; and it returns through   *)
(*  that bind frame by splicing the segment the machine never  *)
(*  removed.                                                            *)
(* ------------------------------------------------------------------ *)

(**
 * **The `Perform` rule, restated with the clause exposed.** Only a restatement
 * of `Hoop.Runtime.Metatheory.step_perform`, but the *shape* is what matters:
 * the continuation is written the way `Hoop.Runtime.Semantics.step` writes it,
 * so F* gives the two the same SMT symbol.
 *)
let ref_perform_shape
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (eff op: string) (payload: list v) (k: rstack v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures
        (match find_prompt eff op k with
          | None -> True
          | Some (captured, clause, below) ->
            step (desugar af afast) (Step (Perform eff op payload) k)
              == Step (desugar af afast clause payload (kont_of captured)) below))
  = MT.step_perform eff op payload k (desugar af afast)

(** **A full clause runs in one reference step**, with the desugaring resolved
    here rather than at the call site. *)
let ref_full_one
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (eff op: string) (payload: list v) (k: rstack v cl)
  : Lemma
      (ensures
        (match find_prompt eff op k with
          | None -> True
          | Some (captured, clause, below) ->
            steps (desugar af afast) 1 (Step (Perform eff op payload) k)
              == Step (desugar af afast clause payload (kont_of captured)) below))
  = match find_prompt eff op k with
    | None -> ()
    | Some (captured, clause, below) ->
      assert (handled_in eff op k);
      assert (steps (desugar af afast) 1 (Step (Perform eff op payload) k)
              == step (desugar af afast) (Step (Perform eff op payload) k));
      MT.step_perform eff op payload k (desugar af afast)

(** **Entering a fast clause body.** `Perform` then `Op`. *)
let ref_fast_two
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (eff op: string) (payload: list v) (k: rstack v cl)
  : Lemma
      (ensures
        (match find_prompt eff op k with
          | None -> True
          | Some (captured, clause, below) ->
            (match clause with
              | Full _ -> True
              | Fast c0 ->
                steps (desugar af afast) 2 (Step (Perform eff op payload) k)
                  == Step (afast c0 payload) (BindF (kont_of captured) :: below))))
  = match find_prompt eff op k with
    | None -> ()
    | Some (captured, clause, below) ->
      assert (handled_in eff op k);
      ref_perform_shape af afast eff op payload k

(** **Leaving a fast clause body.** The reference applies the ctl clause's
    continuation, which is a `Resumed` node, and then splices the segment back on
    -- landing on exactly the stack the machine never took apart. *)
let ref_envf_two
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (eff op: string) (value: v) (k: rstack v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures
        (match find_prompt eff op k with
          | None -> True
          | Some (captured, clause, below) ->
            steps (desugar af afast) 2
              (Step (Var value) (BindF (kont_of captured) :: below))
              == Step (Var value) k))
  = MT.find_prompt_partitions eff op k

(* ------------------------------------------------------------------ *)
(*  12.  The simulation                                                *)
(* ------------------------------------------------------------------ *)

(**
 * **What one machine transition must be**: one *or two* reference
 * transitions, and again a configuration satisfying the invariant.
 *
 * *Never zero.* The machine is a contraction of the reference, not an
 * expansion of it. The two transitions it collapses are exactly the two the
 * desugaring of a fast clause introduces -- `Perform` builds the `Op` node, `Op`
 * pushes its bind frame -- and the two the return through that bind frame costs
 * -- apply the ctl continuation, splice the segment back on. There is therefore
 * no stuttering to rank and no measure to exhibit.
 *
 * *No lambda is written out here, deliberately.* Both sides mention the
 * continuation only through `erase_st` and `steps`, each of which builds it
 * under a `match` on `find_prompt eff op k`. Naming it in the statement would
 * close it over a fresh local binder instead, making it an unrelated SMT symbol.
 *)
let sim_ok (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (q: mstate v cl) : GTot prop =
  Some? (erase_st q) /\
  config_ok (mstep af afast q) /\
  (exists (n: nat).
    (n == 1 \/ n == 2) /\
    erase_st (mstep af afast q)
      == Some (steps (desugar af afast) n (Some?.v (erase_st q))))

(**
 * **The simulation at a `Perform`**, split out so that each of the three
 * dispatch outcomes is proved in a context holding nothing but this transition.
 *
 *   - unhandled: the environment misses exactly when `find_prompt` misses, so
 *     both machines stop. One reference step.
 *   - `Fast`: the body starts running in place under the handler's own
 *     environment, with an `MEnvF` recording the perform site's. Nothing is
 *     captured and the stack is not cut. The reference needs two steps to reach
 *     the same configuration, and the new machine stack erases to exactly what
 *     the reference then has -- which is the point of the whole design.
 *   - `Full`: the existing path, one reference step, exact agreement.
 *)
let msim_perform
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (eff op: string) (payload: list v) (w: menv v cl) (kk: mstack v cl)
  : Lemma
      (requires config_ok (MStep (Perform eff op payload) w kk))
      (ensures sim_ok af afast (MStep (Perform eff op payload) w kk))
  = let apply = desugar af afast in
    let q : mstate v cl = MStep (Perform eff op payload) w kk in
    let Some k = erase_k kk in
    lookup_find eff op k;
    E.lookup_equiv w (env_of_stack k) (eff, op);
    match E.lookup w (eff, op) with
    | None ->
        MT.step_perform_stuck eff op payload k apply;
        introduce exists (n: nat).
          (n == 1 \/ n == 2) /\
          erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
        with 1 and ()
    | Some ev ->
      assert (handled_in eff op k);
      (match lookup_clause (PromptF?.hs ev.E.prompt) eff op with
        | None -> ()
        | Some (Fast c0) ->
            ref_fast_two af afast eff op payload k;
            introduce exists (n: nat).
              (n == 1 \/ n == 2) /\
              erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
            with 2 and ()
        | Some (Full c0) ->
            ref_full_one af afast eff op payload k;
            msplit_agrees eff op kk k;
            introduce exists (n: nat).
              (n == 1 \/ n == 2) /\
              erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
            with 1 and ())

(** **The simulation, one transition.** The main theorem. *)
let msim (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (q: mstate v cl)
  : Lemma (requires config_ok q) (ensures sim_ok af afast q)
  = let apply = desugar af afast in
    match q with
    | MDone x ->
        MT.steps_terminal apply 1 (Done x <: rstate v cl);
        introduce exists (n: nat).
          (n == 1 \/ n == 2) /\
          erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
        with 1 and ()
    | MStuck e o ->
        MT.steps_terminal apply 1 (Stuck e o <: rstate v cl);
        introduce exists (n: nat).
          (n == 1 \/ n == 2) /\
          erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
        with 1 and ()
    | MStep c w kk ->
      let Some k = erase_k kk in
      let s : rstate v cl = Step c k in
      assert (steps apply 1 s == step apply s);
      match c with
      | Perform eff op payload -> msim_perform af afast eff op payload w kk
      | Op comp fn ->
          introduce exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with 1 and ()
      | Handle hs ret body ->
          extend_equiv w (env_of_stack k) (keys hs) (PromptF hs ret <: pd v cl);
          introduce exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with 1 and ()
      | Resumed kont value ->
          erase_inj_append kont kk;
          stack_ok_inj_append kont kk;
          mreinstall_agrees kont k;
          mreinstall_equiv w (env_of_stack k) kont;
          introduce exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with 1 and ()
      | Var value ->
          (match kk with
            | [] ->
                introduce exists (n: nat).
                  (n == 1 \/ n == 2) /\
                  erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
                with 1 and ()
            | MBindF fn :: r ->
                introduce exists (n: nat).
                  (n == 1 \/ n == 2) /\
                  erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
                with 1 and ()
            | MPromptF hs ret :: r ->
                let Some kr = erase_k r in
                pop_env_agrees w hs ret kr;
                introduce exists (n: nat).
                  (n == 1 \/ n == 2) /\
                  erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
                with 1 and ()
            | MEnvF eff op sv :: r ->
                let Some kr = erase_k r in
                ref_envf_two af afast eff op value kr;
                introduce exists (n: nat).
                  (n == 1 \/ n == 2) /\
                  erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
                with 2 and ())

(* ------------------------------------------------------------------ *)
(*  13.  Whole runs                                                     *)
(* ------------------------------------------------------------------ *)

(**
 * **The `Full` branch of `mstep` really is a direct call to the FFI's full
 * interpreter**: `mstep` writes `af c0 payload (kont_of captured)`, so no
 * dispatch survives extraction. The reference machine goes through `desugar`,
 * and this is the equation that makes the two readings agree.
 *)
let full_branch_is_af
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (c0: cl) (payload: list v) (kf: v -> ct v cl)
  : Lemma (desugar af afast (Full c0) payload kf == af c0 payload kf)
  = ()

(** **Loading a program.** The empty environment is the environment of the empty
    stack, so the invariant holds at the start, and the erasure is the reference
    machine's own initial state. *)
let mload (#v #cl: Type) (p: ct v cl)
  : Tot (q: mstate v cl { config_ok q /\ erase_st q == Some (load p) })
  = MStep p E.empty []

(**
 * **The fuel-bounded iteration of `mstep`**, the counterpart of
 * `Hoop.Runtime.Semantics.steps`. `Tot` rather than `GTot` so that the
 * normaliser can run it -- `Hoop.Runtime.Test` does, to check that the two
 * machines really do agree on a program and not merely that they are proved to;
 * `noextract` because the runtime iterates through `mrun`, which needs no fuel.
 *)
noextract
let rec msteps
    (#v #cl: Type)
    (af: full_t v cl)
    (afast: fast_t v cl)
    (fuel: nat)
    (q: mstate v cl)
  : Tot (mstate v cl) (decreases fuel)
  = if fuel = 0
    then q
    else
      match q with
      | MDone _ -> q
      | MStuck _ _ -> q
      | MStep _ _ _ -> msteps af afast (fuel - 1) (mstep af afast q)

(** **Convergence of the reference machine**, restated here because
    `Hoop.Runtime.Laws` deliberately has an empty interface. Identical to
    `Hoop.Runtime.Laws.converges`. *)
let rconverges (#v #cl: Type) (apply: apply_t v cl) (s: state v cl) (x: v) : GTot prop =
  exists (n: nat). steps apply n s == Done x

(** **Convergence of the machine.** *)
let mconverges
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (q: mstate v cl) (x: v)
  : GTot prop
  = exists (n: nat). msteps af afast n q == MDone x

(** **The invariant is preserved by any number of transitions**, and the erased
    run is a run of the reference machine. *)
let rec msteps_agrees
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (fuel: nat) (q: mstate v cl)
  : Lemma
      (requires config_ok q)
      (ensures
        config_ok (msteps af afast fuel q) /\
        Some? (erase_st q) /\
        (exists (n: nat).
          erase_st (msteps af afast fuel q)
            == Some (steps (desugar af afast) n (Some?.v (erase_st q)))))
      (decreases fuel)
  = let apply = desugar af afast in
    if fuel = 0
    then
      introduce exists (n: nat).
        erase_st q == Some (steps apply n (Some?.v (erase_st q)))
      with 0 and ()
    else
      match q with
      | MDone _ | MStuck _ _ ->
          introduce exists (n: nat).
            erase_st q == Some (steps apply n (Some?.v (erase_st q)))
          with 0 and ()
      | MStep _ _ _ ->
          msim af afast q;
          msteps_agrees af afast (fuel - 1) (mstep af afast q);
          eliminate exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with
            eliminate exists (m: nat).
              erase_st (msteps af afast (fuel - 1) (mstep af afast q))
                == Some (steps apply m (Some?.v (erase_st (mstep af afast q))))
            with
              (MT.steps_add apply n m (Some?.v (erase_st q));
               introduce exists (j: nat).
                 erase_st (msteps af afast fuel q)
                   == Some (steps apply j (Some?.v (erase_st q)))
               with (n + m) and ())

(* ------------------------------------------------------------------ *)
(*  14.  The theorem                                                    *)
(* ------------------------------------------------------------------ *)

(** **Soundness**: whatever the machine returns, the reference machine
    returns. *)
let converges_transfer
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (q: mstate v cl) (x: v)
  : Lemma
      (requires config_ok q /\ mconverges af afast q x)
      (ensures rconverges (desugar af afast) (Some?.v (erase_st q)) x)
  = let apply = desugar af afast in
    eliminate exists (n: nat). msteps af afast n q == MDone x
    with
      (msteps_agrees af afast n q;
       eliminate exists (m: nat).
         erase_st (msteps af afast n q) == Some (steps apply m (Some?.v (erase_st q)))
       with
         (introduce exists (j: nat). steps apply j (Some?.v (erase_st q)) == Done x
          with m and ()))

(**
 * **Completeness, and the absence of infinite stuttering**: whatever the
 * reference machine returns, the machine returns.
 *
 * *The measure* is the reference machine's remaining fuel. `msim` says every
 * machine transition is at least one reference transition, so the fuel
 * strictly decreases at every machine step and the recursion terminates. That
 * is the whole ranking argument; no auxiliary measure on machine
 * configurations is needed, because the machine never stutters.
 *)
let rec converges_reflect
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (fuel: nat) (q: mstate v cl) (x: v)
  : Lemma
      (requires
        config_ok q /\
        steps (desugar af afast) fuel (Some?.v (erase_st q)) == Done x)
      (ensures mconverges af afast q x)
      (decreases fuel)
  = let apply = desugar af afast in
    let s = Some?.v (erase_st q) in
    match q with
    | MDone y ->
        MT.steps_terminal apply fuel s;
        introduce exists (n: nat). msteps af afast n q == MDone x with 0 and ()
    | MStuck e o -> MT.steps_terminal apply fuel s
    | MStep _ _ _ ->
        msim af afast q;
        eliminate exists (n: nat).
          (n == 1 \/ n == 2) /\ erase_st (mstep af afast q) == Some (steps apply n s)
        with
          (if fuel <= n
           then
             (MT.steps_stable apply fuel (n - fuel) s;
              introduce exists (j: nat). msteps af afast j q == MDone x with 1 and ())
           else
             (MT.steps_add apply n (fuel - n) s;
              converges_reflect af afast (fuel - n) (mstep af afast q) x;
              eliminate exists (m: nat). msteps af afast m (mstep af afast q) == MDone x
              with
                (introduce exists (j: nat). msteps af afast j q == MDone x
                 with (m + 1) and ())))

(** **The theorem**: the machine and the reference machine agree on
    every program, in both directions. *)
let execute_agrees
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (p: ct v cl) (x: v)
  : Lemma
      (mconverges af afast (mload p) x <==> rconverges (desugar af afast) (load p) x)
  = introduce mconverges af afast (mload p) x ==> rconverges (desugar af afast) (load p) x
    with converges_transfer af afast (mload p) x;
    introduce rconverges (desugar af afast) (load p) x ==> mconverges af afast (mload p) x
    with
      (eliminate exists (n: nat). steps (desugar af afast) n (load p) == Done x
       with converges_reflect af afast n (mload p) x)

(* ------------------------------------------------------------------ *)
(*  15.  Progress                                                       *)
(* ------------------------------------------------------------------ *)

(** **Stuck-freedom survives any number of reference transitions.** *)
let never_stuck_steps (#v #cl: Type) (apply: apply_t v cl) (n: nat) (s: state v cl)
  : Lemma (requires never_stuck apply s) (ensures never_stuck apply (steps apply n s))
  = introduce forall (m: nat). ~(Stuck? (steps apply m (steps apply n s)))
    with MT.steps_add apply n m s

(**
 * **Progress transports**: a machine configuration whose erasure the
 * reference machine never gets stuck from does not get stuck either, and neither
 * does its successor. This is what carries
 * `Hoop.Runtime.Metatheory.progress` -- and with it the whole well-scopedness
 * development -- across to the machine unchanged.
 *)
let mprogress
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (q: mstate v cl)
  : Lemma
      (requires config_ok q /\ never_stuck (desugar af afast) (Some?.v (erase_st q)))
      (ensures
        ~(MStuck? q) /\
        ~(MStuck? (mstep af afast q)) /\
        config_ok (mstep af afast q) /\
        Some? (erase_st (mstep af afast q)) /\
        never_stuck (desugar af afast)
          (Some?.v (erase_st (mstep af afast q))))
  = let apply = desugar af afast in
    let s = Some?.v (erase_st q) in
    never_stuck_now apply s;
    msim af afast q;
    eliminate exists (n: nat).
      (n == 1 \/ n == 2) /\ erase_st (mstep af afast q) == Some (steps apply n s)
    with
      (never_stuck_steps apply n s;
       assert (~(Stuck? (steps apply n s))))

(* ------------------------------------------------------------------ *)
(*  16.  The entry point                                                *)
(* ------------------------------------------------------------------ *)

(* One machine transition is one or two reference transitions, so a run that
   starts after one is a run that starts before it. The counterpart of
   `Hoop.Runtime.Semantics.one_more_step`, with the erasure interposed; kept out
   of the `Div` body below so that the driver reads as the loop it is. *)
private
let one_more_mstep
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (q: mstate v cl) (r: mstate v cl)
  : Lemma
      (requires
        config_ok q /\
        Some? (erase_st (mstep af afast q)) /\
        (exists (m: nat).
          erase_st r
            == Some (steps (desugar af afast) m (Some?.v (erase_st (mstep af afast q))))))
      (ensures
        exists (j: nat).
          erase_st r == Some (steps (desugar af afast) j (Some?.v (erase_st q))))
  = let apply = desugar af afast in
    let s = Some?.v (erase_st q) in
    msim af afast q;
    eliminate exists (n: nat).
      (n == 1 \/ n == 2) /\ erase_st (mstep af afast q) == Some (steps apply n s)
    with
      eliminate exists (m: nat).
        erase_st r == Some (steps apply m (Some?.v (erase_st (mstep af afast q))))
      with
        (MT.steps_add apply n m s;
         introduce exists (j: nat). erase_st r == Some (steps apply j s)
         with (n + m) and ())

(**
 * **The transitive closure**, evidence-driven and tail-resumptive. The only
 * non-ghost iteration of a transition in this module, and the only thing that
 * actually loops at run time.
 *
 * The postcondition is in two parts, and they rest on different assumptions.
 *
 *   - The *simulation* -- `exists n. erase_st r == Some (steps ... n ...)` --
 *     holds of any configuration satisfying the invariant, with no
 *     well-scopedness hypothesis whatever. It is `msim` closed over the loop:
 *     whatever state the machine stops in, the reference machine reaches that
 *     same state on the same input. Stopping in `MStuck` is covered by it, and
 *     says that the reference machine gets stuck there too -- so a stuck run is
 *     a genuinely unhandled operation and not a defect of this machine.
 *
 *   - *Termination in a value* -- `MDone? r` -- is what actually needs
 *     `never_stuck`, and appears guarded by it. `mprogress` is what carries it
 *     from one iteration to the next, and it is invoked only under the guard.
 *
 * Keeping the two apart is what lets `mrun` be called on a configuration
 * nothing is known about and still say something true about the answer. Under
 * `never_stuck` the guard discharges and the conjunction is exactly the older,
 * unconditional-`MDone?` reading.
 *
 * No branch names `MStuck`: it is folded into the catch-all, which is also
 * where `MDone` is returned. `runtime/ml/hoop_ffi.ml` sits outside the type
 * system and hands in a state whose well-scopedness it cannot establish; the
 * catch-all returns whatever it stops at to the FFI -- which reports the
 * unhandled operation -- where an incomplete match would raise `Match_failure`.
 *)
let rec mrun
    (#v #cl: Type)
    (af: full_t v cl)
    (afast: fast_t v cl)
    (q: mstate v cl { config_ok q })
  : Div
      (mstate v cl)
      (requires True)
      (ensures fun r ->
        (exists (n: nat).
          erase_st r == Some (steps (desugar af afast) n (Some?.v (erase_st q)))) /\
        (never_stuck (desugar af afast) (Some?.v (erase_st q)) ==> MDone? r))
  = match q with
    | MStep _ _ _ ->
        msim af afast q;
        let r = mrun af afast (mstep af afast q) in
        one_more_mstep af afast q r;
        introduce
          never_stuck (desugar af afast) (Some?.v (erase_st q)) ==> MDone? r
        with mprogress af afast q;
        r
    | _ ->
        introduce exists (n: nat).
          erase_st q == Some (steps (desugar af afast) n (Some?.v (erase_st q)))
        with 0 and ();
        introduce
          never_stuck (desugar af afast) (Some?.v (erase_st q)) ==> MDone? q
        with never_stuck_now (desugar af afast) (Some?.v (erase_st q));
        q

(**
 * **The entry point the FFI calls**: the machine, loaded and iterated to a
 * value. `runtime/ml/hoop_ffi.ml` calls this and nothing else; it is the whole
 * of the runtime's module boundary.
 *
 * The specification is `Hoop.Runtime.Semantics.steps`, the fuel-bounded
 * iteration of the stack-walking transition, at the desugared reading of the
 * clause table.
 *
 * **There is no precondition.** `execute` runs on any program at all, and the
 * simulation conjunct -- `exists n. erase_st r == Some (steps (desugar af
 * afast) n (load p))` -- holds of every one of them: the erasure of the result
 * is a state the reference machine reaches on that same program, pinned down
 * exactly and not merely as to its shape. This is what covers the branch the
 * FFI actually has to handle. `runtime/ml/hoop_ffi.ml` supplies `p` through
 * `magic`, so it could never have discharged a precondition; with none to
 * discharge, its `MStuck` result is now within the theorem rather than outside
 * it, and the theorem says the reference machine is stuck on that program too.
 * The error it raises therefore reports a real unhandled operation.
 *
 * `MDone? r` is what genuinely needs well-scopedness, and it appears guarded by
 * it: given `never_stuck (desugar af afast) (load p)`, the guard discharges and
 * the result is a value. The standing assumption has moved from "the answer is
 * correct only if PureScript's row types guarantee well-scopedness" to "the
 * answer always agrees with the reference semantics, and PureScript's types are
 * what make `MStuck` unreachable".
 *
 * The two FFI interpreters are the only trusted inputs. `af` is a fully
 * controllable clause, handed the delimited continuation; `afast` is a
 * tail-resumptive one, which is not handed it and cannot be. Which of the two
 * applies is decided by the `clause` tag on the *table entry*, which
 * `handlers_of_js` sets once per `Handle` -- so nothing is assumed of the
 * boundary that F* cannot see.
 *)
let execute
    (#v #cl: Type)
    (af: full_t v cl)
    (afast: fast_t v cl)
    (p: ct v cl)
  : Div
      (mstate v cl)
      (requires True)
      (ensures fun r ->
        (exists (n: nat). erase_st r == Some (steps (desugar af afast) n (load p))) /\
        (never_stuck (desugar af afast) (load p) ==> MDone? r))
  = mrun af afast (mload p)

(* ------------------------------------------------------------------ *)
(*  17.  Non-vacuity: the three scenarios really occur                  *)
(*                                                                     *)
(*  `msim` quantifies over every configuration satisfying `config_ok`,  *)
(*  so it covers the three scenarios of the design -- provided such     *)
(*  configurations exist. This exhibits them, and by the machine's own  *)
(*  transition rather than by hand.                                     *)
(* ------------------------------------------------------------------ *)

(**
 * Two nested handlers: `hsf` (inner) has a *fast* clause for `(ef, opf)`, and
 * `hsg` (outer) has a *full* clause for `(eg, opg)`, which `hsf` does not
 * handle. Performing `(ef, opf)` therefore runs a fast clause body whose effects
 * belong outside its own prompt.
 *
 *   - the fast transition really fires, and really pushes an `MEnvF`
 *     (scenarios 1 and 2 -- a pure body simply returns through it, an effectful
 *     one performs from underneath it);
 *   - the resulting configuration really satisfies `config_ok`, so the `MEnvF`
 *     cases of `msim` are not vacuous;
 *   - performing `(eg, opg)` from inside that body captures the *whole* stack,
 *     the `MEnvF` included (scenario 3): the split leaves nothing behind, so the
 *     `MEnvF` is inside the captured segment and its erasure is what the
 *     reference machine receives -- exhibited here *already erased* into the
 *     `BindF (kont_of ...)` frame it becomes.
 *)
let scenarios_reachable
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (hsf hsg: handlers (clause cl))
    (retf retg: option (v -> ct v cl))
    (ef opf eg opg: string) (payload: list v) (cf cg: cl)
  : Lemma
      (requires
        lookup_clause hsf ef opf == Some (Fast cf) /\
        lookup_clause hsf eg opg == None /\
        lookup_clause hsg eg opg == Some (Full cg))
      (ensures
        (let k0 : rstack v cl = [PromptF hsf retf; PromptF hsg retg] in
         let kk0 : mstack v cl = [MPromptF hsf retf; MPromptF hsg retg] in
         let q0 : mstate v cl = MStep (Perform ef opf payload) (env_of_stack k0) kk0 in
         config_ok q0 /\
         (let q1 = mstep af afast q0 in
          MStep? q1 /\
          Cons? (MStep?.k q1) /\ MEnvF? (hd (MStep?.k q1)) /\
          config_ok q1 /\
          (let q2 : mstate v cl =
             MStep (Perform eg opg payload) (MStep?.w q1) (MStep?.k q1) in
           config_ok q2 /\
           msplit eg opg (MStep?.k q2)
             == Some ([BindF (kont_of [PromptF hsf retf]); PromptF hsg retg], [])))))
  = let k0 : rstack v cl = [PromptF hsf retf; PromptF hsg retg] in
    let kk0 : mstack v cl = [MPromptF hsf retf; MPromptF hsg retg] in
    let q0 : mstate v cl = MStep (Perform ef opf payload) (env_of_stack k0) kk0 in
    assert (erase_k kk0 == Some k0);
    lookup_find ef opf k0;
    fp_prompt_hit ef opf hsf retf [PromptF hsg retg];
    assert (config_ok q0);
    msim af afast q0
