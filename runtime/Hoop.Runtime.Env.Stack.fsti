(**
 * How the evidence environment replaces the stack walk.
 *
 * `Hoop.Runtime.Semantics.find_prompt` answers three questions at once when an operation
 * is performed: which clause handles it, which frames make up the delimited
 * continuation, and which frames remain below. Evidence passing splits them.
 * `Hoop.Runtime.Env.lookup` answers the first in one step. The other two are a
 * *split of the stack*, and no environment can produce a stack; what an
 * evidence gives is the *position* to split at.
 *
 * *Why the position is a height.* The payload of a level records the prompt
 * frame together with the height the stack had when it was installed -- the
 * number of frames below it. A stack of height `n` is then cut into the `n - h`
 * frames pushed inside the handler, the prompt among them, and the `h` that
 * were already there. Two alternatives were rejected. Counting levels of the
 * environment, `depth w - depth ev.below`, is correct only while the
 * environment has exactly one level per prompt on the stack, which is precisely
 * what a tail-resumptive clause body will stop doing. A per-prompt unique tag
 * faithfully models the pointer identity a realisation would test, but makes
 * every prompt carry a name the semantics never uses. A height is neither: the
 * machine already has it, and it stays right when prompts stop being counted.
 *
 * *A height is not a constant.* It is a property of a prompt *relative to the
 * stack it sits on*, and a delimited continuation may be resumed on a stack
 * other than the one it was captured on -- that is what multi-shot means. The
 * heights inside a captured segment are therefore re-derived against the stack
 * in force at the resumption, every time the segment is spliced back on: that
 * is `reinstall`, and what `env_of_stack_append` states. Keeping the captured
 * heights instead is the bug that makes the second resumption of a two-shot
 * clause capture one frame too many.
 *
 * *What is proved.* The central theorem is `step_perform_via_env_agrees`: the
 * transition computed from the environment is *the same state* as the one the
 * stack-walking machine computes. Being a state equality rather than a
 * re-proof, it carries the established properties of `find_prompt` across by
 * rewriting, and `find_prompt` survives as the specification the environment is
 * measured against. What that buys is not speed -- in the model `lookup` walks
 * levels just as `find_prompt` walked frames -- but consistency: evidence never
 * names a prompt that has left the stack, nor fails to name one still on it and
 * visible. `env_matches` and `env_covers` below are the two invariants, the
 * second being the weaker one that survives tail-resumptive clauses, whose body
 * runs with its own prompt on the stack but deliberately out of the
 * environment.
 *)
module Hoop.Runtime.Env.Stack

open FStar.List.Tot
open Hoop.Runtime.Syntax
open Hoop.Runtime.Semantics
open Hoop.Runtime.WellScopedness

module E = Hoop.Runtime.Env

(** **A prompt frame**: the `PromptF` frames, as a type. The whole frame rather
    than just its table, because a scoped operation reinstalls the return clause
    too. *)
let prompt (v cl: Type) = f: frame v cl { PromptF? f }

(**
 * **What a level of the environment carries**: a prompt frame and the height
 * the stack had underneath it when it was installed. This is the machine's
 * choice of payload, not the environment's -- see the header of
 * `Hoop.Runtime.Env` on why the payload is a parameter.
 *)
noeq
type pframe (v cl: Type) = {
  pf : prompt v cl;
  h  : nat;
}

(* ------------------------------------------------------------------ *)
(*  The environment a stack offers                                     *)
(* ------------------------------------------------------------------ *)

(**
 * **The environment a stack offers**: one level per prompt frame, innermost
 * first, each recording the height of the stack below it. This is what the
 * machine's environment component is equal to -- exactly, until tail-resumptive
 * clauses arrive, and up to `env_covers` afterwards.
 *
 * `noextract` because no transition calls it. A `let` in an interface is
 * extracted on its own rather than with its callers, so without the qualifier a
 * definition that walks the whole stack would ship unreachable.
 *)
noextract
let rec env_of_stack (#v #cl: Type) (k: stack v cl)
  : Tot (E.env (pframe v cl)) (decreases k)
  = match k with
    | [] -> E.empty
    | BindF _ :: rest -> env_of_stack rest
    | PromptF hs ret :: rest ->
        E.extend (env_of_stack rest) (keys hs)
          ({ pf = (PromptF hs ret <: prompt v cl); h = length rest })

(**
 * **Installing the prompts of a segment onto an environment**, outermost
 * first, with their heights measured from `base`: the model of resumption,
 * which walks a captured segment from its bottom and re-derives evidence
 * against the *current* environment and the *current* stack height. Written as
 * a fold from the head of the list -- the top of the segment -- because a stack
 * is innermost-first, so the recursive call handles the outer frames and the
 * head extends last.
 *
 * `base` is the height of the stack the segment is spliced onto, which is why
 * this is not `env_of_stack` of the segment: the same segment resumed twice,
 * under stacks of different heights, yields different heights both times.
 *
 * `n` is the height of `k`, threaded rather than measured -- the same
 * bookkeeping as `split_at_height` below, and for the same reason; reading the
 * height off with `length rest` at every frame would turn one walk of the
 * segment into one walk per prompt on it. Here the equation is a refinement
 * rather than left unchecked, since `reinstall` is only ever applied to a
 * segment the caller has just measured, and carrying the assumption in the type
 * saves restating it in every lemma below.
 *
 * This stays the *specification*: it recurses to the bottom of the segment
 * before extending anything, which is the shape the equations below want and a
 * recursion as deep as the segment is long. What the machine runs is
 * `reinstall_fast`, proved equal to it at the end of this interface;
 * `noextract` is what keeps the slower and deeper of the two from shipping.
 *)
noextract
let rec reinstall
    (#v #cl: Type)
    (base: nat)
    (w: E.env (pframe v cl))
    (k: stack v cl)
    (n: nat { n == length k })
  : Tot (E.env (pframe v cl)) (decreases k)
  = match k with
    | [] -> w
    | BindF _ :: rest -> reinstall base w rest (n - 1)
    | PromptF hs ret :: rest ->
        E.extend (reinstall base w rest (n - 1)) (keys hs)
          ({ pf = (PromptF hs ret <: prompt v cl); h = base + (n - 1) })

(**
 * **Splitting a stack at a height**, the prompt included in the first
 * component -- deep-handler semantics, exactly as `find_prompt` does it. The
 * frames pushed since the handler was installed are cut off, and the `h` frames
 * that were there before it remain.
 *
 * *`n` is the height of `k`, and is passed in rather than measured.* That is
 * the point of the whole phase: `length k` walks the entire stack, the frames
 * *below* the handler included, which are exactly the ones evidence passing was
 * meant to stop looking at, and measuring here would restore the cost
 * `Hoop.Runtime.Semantics.find_prompt` was replaced to remove. The machine already has
 * the number -- `Hoop.Runtime.config.ht` tracks it, and `config_ok`
 * proves it equal to `length k`.
 *
 * Nothing here checks that it is, nor that `h` is in range: the definition is
 * total on any `n` and any `h`, which keeps
 * `Hoop.Runtime.step_env` a total function of a configuration with no
 * precondition to discharge -- the same reasoning as the guards in `pop_env`
 * there. The equation belongs with correctness instead: every lemma below that
 * says anything about the result assumes `n == length k`, and the machine
 * discharges that from its invariant.
 *)
let split_at_height (#v #cl: Type) (h: nat) (k: stack v cl) (n: nat)
  : Tot (stack v cl & stack v cl)
  = if h >= n then ([], k) else splitAt (n - h) k

(* ------------------------------------------------------------------ *)
(*  The correspondence                                                 *)
(* ------------------------------------------------------------------ *)

(**
 * **Dispatch agrees**: the environment finds a handler exactly when the stack
 * has one. Right to left it is soundness (no evidence is invented), left to
 * right completeness (no handler is hidden), and it is what keeps the `Stuck`
 * branch of `step` in step with the environment's `None`.
 *)
val lookup_iff_handled (#v #cl: Type) (eff op: string) (k: stack v cl)
  : Lemma (Some? (E.lookup (env_of_stack k) (eff, op)) <==> handled_in eff op k)

(**
 * **The environment finds the same prompt and the same clause** that
 * `find_prompt` does -- the last frame of the captured segment, which
 * `find_prompt_last` identifies as the prompt owning the clause. Combined with
 * `find_prompt_innermost` this is handler shadowing: shadowing in the
 * environment and innermost-prompt selection on the stack pick the same
 * handler.
 *)
let lookup_finds_prompt_correctness (#v #cl: Type) (eff op: string) (k: stack v cl) : prop =
  handled_in eff op k ==>
    (match E.lookup (env_of_stack k) (eff, op) with
      | None -> False
      | Some ev ->
          let Some (cap, c, _) = find_prompt eff op k in
          Cons? cap /\
          ev.E.prompt.pf == last cap /\
          lookup_clause (PromptF?.hs ev.E.prompt.pf) eff op == Some c)

val lookup_finds_prompt (#v #cl: Type) (eff op: string) (k: stack v cl)
  : Lemma (lookup_finds_prompt_correctness eff op k)

(**
 * **The recorded height is the height of the stack below the prompt**: the
 * evidence remembers exactly how many frames `find_prompt` would leave behind.
 * This is what makes the split a subtraction rather than a search.
 *)
let lookup_height_correctness (#v #cl: Type) (eff op: string) (k: stack v cl) : prop =
  handled_in eff op k ==>
    (match E.lookup (env_of_stack k) (eff, op) with
      | None -> False
      | Some ev ->
          let Some (_, _, below) = find_prompt eff op k in
          ev.E.prompt.h == length below)

val lookup_height (#v #cl: Type) (eff op: string) (k: stack v cl)
  : Lemma (lookup_height_correctness eff op k)

(** **The evidence's `below` is the environment of the stack below**: the
    context a clause runs in is the context the prompt was installed in,
    whichever way it is computed. The clause a broken evidence-passing
    implementation gets wrong. *)
let lookup_below_correctness (#v #cl: Type) (eff op: string) (k: stack v cl) : prop =
  handled_in eff op k ==>
    (match E.lookup (env_of_stack k) (eff, op) with
      | None -> False
      | Some ev ->
          let Some (_, _, below) = find_prompt eff op k in
          ev.E.below `E.equiv` env_of_stack below)

val lookup_below (#v #cl: Type) (eff op: string) (k: stack v cl)
  : Lemma (lookup_below_correctness eff op k)

(**
 * **The evidence-driven split is `find_prompt`'s split**: cutting the stack at
 * the height the evidence records produces exactly the two pieces the search
 * produced. This is the lemma that lets the handler search be deleted from the
 * `Perform` rule while `find_prompt_partitions` and `find_prompt_last` keep
 * their meaning.
 *
 * The stack's own height is a parameter, constrained to be what it is: this is
 * where the assumption `split_at_height` does not check is written down, for
 * everything downstream of it.
 *)
let split_at_height_correctness (#v #cl: Type) (eff op: string) (k: stack v cl) (n: nat) : prop =
  (n == length k /\ handled_in eff op k) ==>
    (match E.lookup (env_of_stack k) (eff, op) with
      | None -> False
      | Some ev ->
          let Some (cap, _, below) = find_prompt eff op k in
          split_at_height ev.E.prompt.h k n == (cap, below))

val split_at_height_agrees (#v #cl: Type) (eff op: string) (k: stack v cl) (n: nat)
  : Lemma (split_at_height_correctness eff op k n)

(* ------------------------------------------------------------------ *)
(*  The transition                                                     *)
(* ------------------------------------------------------------------ *)

(**
 * **The handler search, done by evidence rather than by walking.** The whole of
 * `find_prompt`'s answer -- captured segment, clause, remaining stack --
 * assembled from one evidence and one subtraction, with no frame inspected
 * except by the split, and none at all below the prompt. `n` is the height of
 * `k`, threaded through from the caller that tracks it; see `split_at_height`.
 *
 * The argument is the *payload* of the evidence, not the evidence:
 * `Hoop.Runtime.Env.lookup` pins the payload down up to `==` but the
 * accompanying environment only up to `equiv`, so taking the payload is what
 * lets the machine run this on its own environment and land on the same triple.
 *
 * The `None` branch -- an evidence whose table has no clause for the key that
 * found it -- is unreachable under `env_well_keyed`, and is written out rather
 * than eliminated for the same reason `Hoop.Runtime.run_env` keeps a catch-all.
 *)
let perform_split
    (#v #cl: Type)
    (p: pframe v cl)
    (eff op: string)
    (k: stack v cl)
    (n: nat)
  : Tot (option (stack v cl & cl & stack v cl))
  = match lookup_clause (PromptF?.hs p.pf) eff op with
    | None -> None
    | Some clause ->
        let (captured, below) = split_at_height p.h k n in
        Some (captured, clause, below)

(** **The central theorem**: evidence answers the question `find_prompt`
    answers, with the very same triple. An equality of plain data, deliberately:
    saying nothing about lambdas, it transports through anything built from the
    triple -- `step_perform_via_env` below, then `Hoop.Runtime`. *)
val perform_split_agrees
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
    (n: nat)
  : Lemma
      (requires Some? (E.lookup (env_of_stack k) (eff, op)) /\ n == length k)
      (ensures
        perform_split (Some?.v (E.lookup (env_of_stack k) (eff, op))).E.prompt eff op k n
          == find_prompt eff op k)

(**
 * **The `Perform` rule, driven by evidence.**
 *
 * *The shape of this definition is load-bearing.* It repeats, branch for branch,
 * the `Perform` case of `Hoop.Runtime.Semantics.step`, differing only in the scrutinee,
 * and names the delimited continuation the same way `step` does -- through
 * `Hoop.Runtime.Semantics.kont_of`. Writing it out as `fun x -> Resumed captured x`
 * instead would give it an SMT symbol closing over the *scrutinee* rather than
 * the pattern variable (see the comment on `kont_of`), so that connecting it to
 * the one `step` builds would rest on the two matches happening to elaborate
 * identically. Going through the named function makes both sides literally the
 * same term once `perform_split_agrees` equates the scrutinees.
 *
 * The environment the clause runs under is not returned -- it is `ev.below` of
 * the evidence that produced `p`, which the caller already holds. Keeping it
 * out is what lets this have exactly `step`'s shape.
 *)
let step_perform_via_env
    (#v #cl: Type)
    (apply: apply_t v cl)
    (eff op: string)
    (payload: list v)
    (p: pframe v cl)
    (k: stack v cl)
    (n: nat)
  : Tot (state v cl)
  = match perform_split p eff op k n with
    | None -> Stuck eff op
    | Some (captured, clause, below) ->
        Step (apply clause payload (kont_of captured)) below

(**
 * **The evidence-driven `Perform` rule computes the very state the
 * stack-driven one computes.** Being a state equality, it carries every
 * property already proved of the old rule across without re-proof --
 * everything downstream in `Hoop.Runtime.Metatheory`, `progress` included, is a
 * statement about the state `step` returns.
 *)
val step_perform_via_env_agrees
    (#v #cl: Type)
    (apply: apply_t v cl)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (n: nat)
  : Lemma
      (requires Some? (E.lookup (env_of_stack k) (eff, op)) /\ n == length k)
      (ensures
        step_perform_via_env apply eff op payload
          (Some?.v (E.lookup (env_of_stack k) (eff, op))).E.prompt k n
          == step apply (Step (Perform eff op payload) k))

(* ------------------------------------------------------------------ *)
(*  Invariants                                                         *)
(* ------------------------------------------------------------------ *)

(**
 * **Exact agreement**: the machine's environment is the environment its stack
 * offers -- only up to `equiv`, since the machine's environment is built
 * incrementally by `extend` and popped as prompts leave, and there is no reason
 * for it to be the same *value* as one rebuilt from the stack. This is the
 * invariant `Hoop.Runtime` carries: the environment gains and loses a
 * level exactly when the stack gains and loses a prompt.
 *)
let env_matches (#v #cl: Type) (w: E.env (pframe v cl)) (k: stack v cl) : GTot prop =
  w `E.equiv` env_of_stack k

(**
 * **Order-preserving sublist**: `s` is obtained from `l` by deleting elements.
 * Used only to say that the levels of an environment are *some* of the prompts
 * on the stack, in their stack order.
 *)
let rec sublist_of (#a: Type) (s l: list a) : Tot prop (decreases l) =
  match l with
  | [] -> s == []
  | y :: l' ->
      (match s with
        | [] -> True
        | x :: s' -> (x == y /\ sublist_of s' l') \/ sublist_of s l')

(** **The prompts of a stack**, innermost first. `noextract` for the reason
    `env_of_stack` is: it states an invariant, and no transition computes it. *)
noextract
let rec prompts_of (#v #cl: Type) (k: stack v cl) : Tot (list (prompt v cl)) (decreases k) =
  match k with
  | [] -> []
  | PromptF hs ret :: rest -> (PromptF hs ret <: prompt v cl) :: prompts_of rest
  | _ :: rest -> prompts_of rest

(** **The prompts an environment names**, innermost first. *)
let env_prompts (#v #cl: Type) (w: E.env (pframe v cl)) : GTot (list (prompt v cl)) =
  map (fun (l: E.level (pframe v cl)) -> l.E.payload.pf) (E.levels w)

(**
 * **Coverage**: every prompt the environment names is still a live frame of the
 * stack, and the environment lists them in stack order.
 *
 * The weak invariant -- the one that survives what comes later. It does *not*
 * say the environment names every prompt on the stack, and it must not: a
 * tail-resumptive clause body runs with its own prompt on the stack but out of
 * the environment on purpose, because effects raised there belong to the
 * handler's context and must not be captured by handlers installed between the
 * perform site and the prompt. Coverage is the half of the correspondence that
 * may never be given up -- its failure is evidence pointing at a prompt that is
 * not on the stack.
 *)
let env_covers (#v #cl: Type) (w: E.env (pframe v cl)) (k: stack v cl) : GTot prop =
  env_prompts w `sublist_of` prompts_of k

(**
 * **A payload is where it says it is**: the prompt frame sits on `k` with
 * exactly `h` frames below it. This is what makes `split_at_height` cut at the
 * right frame, and it is the part of the correspondence that a height, unlike
 * a count of prompts, keeps once the environment stops naming every prompt.
 *)
let located_in (#v #cl: Type) (p: pframe v cl) (k: stack v cl) : GTot prop =
  exists (above below: stack v cl).
    k == above @ (p.pf :: below) /\ length below == p.h

let env_located (#v #cl: Type) (w: E.env (pframe v cl)) (k: stack v cl) : GTot prop =
  forall (l: E.level (pframe v cl)). l `memP` E.levels w ==> located_in l.E.payload k

(**
 * **Well-keyedness of a level**: a level binds precisely the keys its own
 * handler table has clauses for -- no key without a clause (which would make
 * dispatch invent a handler) and no clause without a key (which would make an
 * operation unreachable even though a handler for it is in scope).
 *)
let level_well_keyed (#v #cl: Type) (l: E.level (pframe v cl)) : prop =
  forall (eff op: string).
    ((eff, op) `mem` l.E.keys) <==> Some? (lookup_clause (PromptF?.hs l.E.payload.pf) eff op)

let env_well_keyed (#v #cl: Type) (w: E.env (pframe v cl)) : GTot prop =
  forall (l: E.level (pframe v cl)). l `memP` E.levels w ==> level_well_keyed l

(** **The machine's environment invariant**, in the form the evidence-passing
    machine is meant to carry once tail-resumptive clauses make `env_matches`
    too strong. *)
let env_ok (#v #cl: Type) (w: E.env (pframe v cl)) (k: stack v cl) : GTot prop =
  env_covers w k /\ env_located w k /\ env_well_keyed w

(** **The environment a stack offers is well keyed** --
    `Hoop.Runtime.Handlers.keys_correct`, lifted over `env_of_stack`. *)
val env_of_stack_well_keyed (#v #cl: Type) (k: stack v cl)
  : Lemma (env_well_keyed (env_of_stack k))

(** **The environment a stack offers names exactly its prompts**, in order. The
    exact form of coverage, of which `env_covers` keeps only what survives. *)
val env_prompts_of_stack (#v #cl: Type) (k: stack v cl)
  : Lemma (env_prompts (env_of_stack k) == prompts_of k)

(** **Exact agreement is the strongest form of the invariant.** *)
val env_matches_implies_ok (#v #cl: Type) (w: E.env (pframe v cl)) (k: stack v cl)
  : Lemma (requires env_matches w k) (ensures env_ok w k)

(** **Evidence never dangles**: under coverage, the prompt an evidence names is
    a frame of the stack -- which is what makes the split well defined. *)
val evidence_live (#v #cl: Type) (w: E.env (pframe v cl)) (k: stack v cl) (eff op: string)
  : Lemma
      (requires env_ok w k /\ Some? (E.lookup w (eff, op)))
      (ensures
        (Some?.v (E.lookup w (eff, op))).E.prompt.pf `memP` k /\
        located_in (Some?.v (E.lookup w (eff, op))).E.prompt k)

(**
 * **Evidence never lies about its clause**: under well-keyedness, a successful
 * lookup names a prompt whose table really does have a clause for the key. This
 * is what makes the inner `None` of `step_perform_via_env` unreachable.
 *)
val evidence_has_clause (#v #cl: Type) (w: E.env (pframe v cl)) (eff op: string)
  : Lemma
      (requires env_well_keyed w /\ Some? (E.lookup w (eff, op)))
      (ensures
        Some? (lookup_clause
                 (PromptF?.hs (Some?.v (E.lookup w (eff, op))).E.prompt.pf) eff op))

(** **A located evidence splits the stack where `find_prompt` would.** The
    coverage-side counterpart of `split_at_height_agrees`: it needs only that
    the payload is where it says it is, so it is the form that survives where
    `env_matches` does not. *)
val split_at_height_located (#v #cl: Type) (p: pframe v cl) (k: stack v cl) (n: nat)
  : Lemma
      (requires located_in p k /\ n == length k)
      (ensures
        (let (cap, below) = split_at_height p.h k n in
          cap @ below == k /\
          length below == p.h /\
          Cons? cap /\
          last cap == p.pf))

(* ------------------------------------------------------------------ *)
(*  Preservation                                                       *)
(*                                                                     *)
(*  One clause per transition of `step`. Together they are what         *)
(*  `Hoop.Runtime.step_env_agrees` is assembled from, in the    *)
(*  same shape as `step_preserves_wf` in `Hoop.Runtime.Metatheory`.     *)
(* ------------------------------------------------------------------ *)

(** **`Perform`**: the environment the evidence leaves behind agrees with the
    stack the split leaves behind -- which is what makes `env_matches` an
    invariant across a `Perform`. *)
val perform_preserves_env_matches
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
    (n: nat)
  : Lemma
      (requires Some? (E.lookup (env_of_stack k) (eff, op)) /\ n == length k)
      (ensures
        (let ev = Some?.v (E.lookup (env_of_stack k) (eff, op)) in
          match perform_split ev.E.prompt eff op k n with
          | None -> True
          | Some (_, _, below) ->
              env_matches ev.E.below below /\ ev.E.prompt.h == length below))

(** **`Op`**: a bind frame contributes no level. *)
val env_matches_bind (#v #cl: Type) (w: E.env (pframe v cl)) (k: stack v cl)
                     (fn: v -> comp_tree v cl)
  : Lemma (requires env_matches w k) (ensures env_matches w (BindF fn :: k))

(** **`Handle`**: one prompt, one level, keyed by the whole table at once --
    which is why leaving the handler pops exactly one level -- and stamped with
    the height the stack has at the moment of installation. *)
val env_matches_handle (#v #cl: Type) (w: E.env (pframe v cl)) (k: stack v cl)
                       (hs: handlers cl) (ret: option (v -> comp_tree v cl))
  : Lemma
      (requires env_matches w k)
      (ensures
        env_matches
          (E.extend w (keys hs) ({ pf = (PromptF hs ret <: prompt v cl); h = length k }))
          (PromptF hs ret :: k))

(**
 * **Leaving a prompt**: popping a `PromptF` pops one level. An implementation
 * that pops the wrong number of levels is caught here. The conclusion is stated
 * over every environment that is `w` minus one level, which is exactly what
 * `Hoop.Runtime.Env.outer` is specified to be.
 *)
val env_matches_pop (#v #cl: Type) (w: E.env (pframe v cl)) (k: stack v cl)
                    (hs: handlers cl) (ret: option (v -> comp_tree v cl))
  : Lemma
      (requires env_matches w (PromptF hs ret :: k))
      (ensures
        E.depth w == E.depth (env_of_stack k) + 1 /\
        (forall (w': E.env (pframe v cl)).
          (exists (l: E.level (pframe v cl)). E.levels w == l :: E.levels w') ==>
          env_matches w' k))

(** **`Resumed`**: the machine's incremental `reinstall` and the environment of
    the spliced stack agree, as *values*, so no `equiv` reasoning is needed at
    the one transition where the environment is rebuilt. *)
val env_of_stack_append (#v #cl: Type) (k1 k2: stack v cl)
  : Lemma (env_of_stack (k1 @ k2) == reinstall (length k2) (env_of_stack k2) k1 (length k1))

(** **Reinstalling respects `equiv`**, which is what lets the machine reinstall
    onto its own environment rather than onto one rebuilt from the stack. *)
val reinstall_equiv
    (#v #cl: Type)
    (base: nat)
    (w1 w2: E.env (pframe v cl))
    (k: stack v cl)
    (n: nat { n == length k })
  : Lemma
      (requires w1 `E.equiv` w2)
      (ensures reinstall base w1 k n `E.equiv` reinstall base w2 k n)

(**
 * **The loop that installs a segment**, and the only part of `reinstall_fast`
 * with any content.
 *
 * `rk` is the segment *outermost frame first* -- the order levels have to be
 * pushed in, since `Hoop.Runtime.Env.extend` pushes onto the front and the
 * innermost prompt must end up there. `j` counts the frames already installed,
 * which is exactly the number beneath the one in hand, so `base + j` is the
 * height `reinstall` stamps it with. The count goes up at every frame, bind
 * frames included: a height counts frames, not prompts.
 *)
let rec reinstall_loop
    (#v #cl: Type)
    (base: nat)
    (w: E.env (pframe v cl))
    (j: nat)
    (rk: stack v cl)
  : Tot (E.env (pframe v cl)) (decreases rk)
  = match rk with
    | [] -> w
    | BindF _ :: rest -> reinstall_loop base w (j + 1) rest
    | PromptF hs ret :: rest ->
        reinstall_loop base
          (E.extend w (keys hs) ({ pf = (PromptF hs ret <: prompt v cl); h = base + j }))
          (j + 1) rest

(** **The loop over the reversed segment is the specification.** Stated here,
    rather than left inside the proof of `reinstall_fast`, only because
    `reinstall_fast` has to be a definition rather than a `val` -- see there. *)
val reinstall_loop_rev (#v #cl: Type) (base: nat) (w: E.env (pframe v cl)) (k: stack v cl)
  : Lemma (reinstall_loop base w 0 (rev k) == reinstall base w k (length k))

(**
 * **The same environment, built without recursing over the segment**: what the
 * machine actually runs at a `Resumed`.
 *
 * `reinstall` recurses to the bottom of the captured segment before extending
 * anything, so its recursion is as deep as the segment is long -- and the
 * extracted runtime maps that depth onto the host's call stack, a few tens of
 * thousands of frames that are the user's to spend, not the machine's. This
 * computes the same environment with two loops instead: `rev` reverses the
 * segment (itself a loop, in `runtime/ml/shim/FStar_List_Tot_Base.ml`) and
 * `reinstall_loop` installs it in one accumulating pass.
 *
 * The equality is in the type rather than in a lemma beside it, so that every
 * statement above about `reinstall` is a statement about this with no transport
 * step to write. `length k` in the refinement is erased with it: the loop
 * counts up from the bottom of the segment and never needs the total.
 *
 * *Why this is a definition and not a `val`.* `Hoop.Runtime.Test` runs the
 * machine under the normaliser and checks it lands on the same state as the
 * stack-walking one. An abstract `val` stops the normaliser dead -- no body to
 * unfold, and the equation in its refinement is an SMT fact `assert_norm` does
 * not consult. Every function on the machine's path is therefore transparent.
 *)
let reinstall_fast (#v #cl: Type) (base: nat) (w: E.env (pframe v cl)) (k: stack v cl)
  : Tot (w': E.env (pframe v cl) { w' == reinstall base w k (length k) })
  = reinstall_loop_rev base w k;
    reinstall_loop base w 0 (rev k)

(* ------------------------------------------------------------------ *)
(*  Bridge to well-scopedness                                          *)
(* ------------------------------------------------------------------ *)

(**
 * **The capability environment an evidence environment offers.** The
 * evidence-passing counterpart of `Hoop.Runtime.WellScopedness.can_in`, which
 * is defined by a `find_prompt` search.
 *)
let can_env (#v #cl: Type) (w: E.env (pframe v cl)) : GTot can_perform =
  fun eff op -> Some? (E.lookup w (eff, op))

(**
 * **The two capability environments coincide**, hence -- by the already proved
 * `Hoop.Runtime.WellScopedness.ws_cong_eq` and `wf_stack_cong_eq` -- `ws` and
 * `wf_stack` may be re-indexed by the evidence environment without disturbing
 * a line of the progress development.
 *)
val can_env_agrees (#v #cl: Type) (k: stack v cl)
  : Lemma (equiv_can (can_env (env_of_stack k)) (can_in k))
