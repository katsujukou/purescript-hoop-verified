(**
 * The monad laws, and the algebraicity of operations, for the Hoop runtime.
 *
 * The three laws are *not* equalities of computation trees: `Op (Var a) fn` and
 * `fn a` are different trees, and the machine visits different configurations
 * on the way. What is claimed is *observational* equivalence: plugged into the
 * same continuation, the two sides either both diverge or both come back with
 * the same value. "Any continuation" means any stack, and since handlers live
 * on the stack as `PromptF` frames, that quantification *is* the quantification
 * over handler contexts -- which a test suite can only sample.
 *
 * What is proved:
 *
 *   - `left_identity`      `pure a >>= fn ~ fn a`                  -- unconditionally
 *   - `right_identity`     `m >>= pure ~ m`                        -- under `apply_obs_congr`
 *   - `associativity`      `(m >>= f) >>= g ~ m >>= (f >=> g)`     -- under `apply_obs_congr`
 *   - `perform_algebraic`  operations commute with binds           -- corollary of the above
 *   - `handle_not_algebraic`  `Handle` does *not*                  -- a concrete refutation
 *
 * `apply_obs_congr` is a condition on the FFI parameter `apply`, in the same
 * spirit as `Hoop.Runtime.apply_ok`, and is discussed where it is defined. It
 * is not vacuous: `lapply_obs_congr` exhibits a four-clause `apply` satisfying
 * it -- the same `apply` that refutes algebraicity of `Handle`, so that failure
 * cannot be blamed on an unsatisfiable hypothesis.
 *
 * *A word on closures.* Several statements below go out of their way not to
 * write down a lambda that the machine also writes down (`kont_of`,
 * `apply_pointwise`, the `LAddAfter` case of `lapply_obs_congr`). F* gives each
 * anonymous function an opaque SMT symbol determined by its elaborated shape,
 * closing over its free variables -- and for a lambda under a `match`, the free
 * variable is the *scrutinee*, not the pattern variable. Two lambdas that agree
 * pointwise are then unrelated symbols, and function extensionality is not
 * available to connect them.
 *)
module Hoop.Runtime.Laws

friend Hoop.Runtime.Handlers

open Hoop.Runtime
open Hoop.Runtime.Properties
open FStar.List.Tot

// ------------------------------------------------------------------ //
//  Observation                                                        //
// ------------------------------------------------------------------ //

(**
 * **Convergence**: the machine, started at `s`, eventually stops with `x`.
 * `steps` is fuel-indexed, so "eventually" is an existential over the fuel;
 * `steps_stable` makes the choice of fuel immaterial.
 *)
let converges (#v #cl: Type) (apply: apply_t v cl) (s: state v cl) (x: v) : GTot prop =
  exists (n: nat). steps apply n s == Done x

(** **A machine run has at most one result**: the longer of two stopping runs is
    the shorter one continued, and `Done` is a fixed point of `step`. *)
let converges_det
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
    (x y: v)
  : Lemma (requires converges apply s x /\ converges apply s y) (ensures x == y)
  = eliminate exists (n: nat). steps apply n s == Done x
    returns x == y
    with _.
      eliminate exists (m: nat). steps apply m s == Done y
      returns x == y
      with _.
        if n <= m then steps_stable apply n (m - n) s
        else steps_stable apply m (n - m) s

(**
 * **Observational approximation, at a fixed observation depth.**
 * `obs_le_n apply n c1 c2` reads: whenever `c1`, in any continuation, reaches a
 * value within `n` transitions, `c2` reaches the same value in that same
 * continuation -- eventually, with no bound.
 *
 * The quantification over the stack `k` is the whole point: a stack is where
 * handlers live, so ranging over every `k` is ranging over every handler
 * context.
 *
 * The index `n` bounds only the *left* run. It is what makes `apply_obs_congr`
 * below usable as an induction hypothesis; `obs_le` closes over it and is the
 * notion one actually reads.
 *)
let obs_le_n
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n: nat)
    (c1 c2: comp_tree v cl)
  : GTot prop
  = forall (k: stack v cl) (x: v).
      steps apply n (Step c1 k) == Done x ==> converges apply (Step c2 k) x

(** **Observational approximation**: `c2` does everything `c1` does. *)
let obs_le (#v #cl: Type) (apply: apply_t v cl) (c1 c2: comp_tree v cl) : GTot prop =
  forall (k: stack v cl) (x: v). converges apply (Step c1 k) x ==> converges apply (Step c2 k) x

(** **Observational equivalence**, written `c1 ~ c2` in the comments below. *)
let obs_eq (#v #cl: Type) (apply: apply_t v cl) (c1 c2: comp_tree v cl) : GTot prop =
  obs_le apply c1 c2 /\ obs_le apply c2 c1

(** Approximation at every depth is approximation. *)
let obs_le_of_n
    (#v #cl: Type)
    (apply: apply_t v cl)
    (c1 c2: comp_tree v cl)
  : Lemma (requires forall (n: nat). obs_le_n apply n c1 c2) (ensures obs_le apply c1 c2)
  = ()

(** ... and conversely, so the indexed notion is a genuine stratification. *)
let obs_le_n_of
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n: nat)
    (c1 c2: comp_tree v cl)
  : Lemma (requires obs_le apply c1 c2) (ensures obs_le_n apply n c1 c2)
  = ()

let obs_le_refl (#v #cl: Type) (apply: apply_t v cl) (c: comp_tree v cl)
  : Lemma (obs_le apply c c)
  = ()

let obs_eq_refl (#v #cl: Type) (apply: apply_t v cl) (c: comp_tree v cl)
  : Lemma (obs_eq apply c c)
  = ()

(**
 * **The index is downward closed**: an approximation good to depth `n` is good
 * to any smaller depth, because a run that stops in `m` transitions is still
 * stopped, at the same value, after `n`. This is what lets a proof spend part
 * of the budget on a transition and carry the rest.
 *)
let obs_le_n_mono
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n m: nat)
    (c1 c2: comp_tree v cl)
  : Lemma (requires obs_le_n apply n c1 c2 /\ m <= n) (ensures obs_le_n apply m c1 c2)
  = introduce forall (k: stack v cl) (x: v).
      (steps apply m (Step c1 k) == Done x ==> converges apply (Step c2 k) x)
    with introduce _ ==> _
    with _. steps_stable apply m (n - m) (Step c1 k)

// ------------------------------------------------------------------ //
//  The condition imposed on the FFI parameter `apply`                 //
// ------------------------------------------------------------------ //

(**
 * **`apply` respects the continuation, level by level.**
 *
 * Like `apply_ok` in `Hoop.Runtime`, this is a condition on the FFI boundary,
 * not a theorem: `apply` hands the payload and the captured continuation to an
 * opaque PureScript closure whose body F* never sees. It appears only as a
 * hypothesis of the laws below.
 *
 * *Why it is needed at all.* Consider right identity, `Op m Var ~ m`. Stepping
 * the left side pushes a `BindF Var` frame the right side does not have; if `m`
 * performs an operation, `find_prompt` packages everything above the handling
 * prompt as the delimited continuation, and that extra frame is *inside the
 * package*. The clause therefore receives literally different continuations on
 * the two sides, and `apply` is a black box, so nothing can be said about the
 * results unless something is assumed. Associativity is the same story.
 * (Left identity needs no assumption: there the extra frame is consumed two
 * transitions later, before any operation can see it.)
 *
 * *Why the index.* The unindexed phrasing is too weak to use. The proof below
 * inducts on the length of the left-hand run, and where the assumption is
 * invoked it has only what the induction hypothesis supplies about the two
 * continuations: `obs_le_n` at a strictly smaller index. Feeding that to an
 * unindexed hypothesis would require the very statement being proved, at every
 * index. Demanding that `apply` preserve the index breaks the circle.
 *
 * It is a causality condition -- the result of `apply` may not converge in `n`
 * transitions by consulting behaviour of the continuation that shows up only
 * after more than `n` -- and it is *stronger* than the unindexed reading, which
 * it implies. What is assumed is not merely that `apply` respects observation,
 * but that it does so uniformly in the depth at which it is observed.
 *
 * `lapply_obs_congr` at the bottom of this file verifies the condition for a
 * concrete `apply`, and records the one clause shape its check does not cover.
 * Note finally that `obs_le_n`, hence this condition, is directional: the two
 * directions of each law are proved separately.
 *)
let apply_obs_congr (#v #cl: Type) (apply: apply_t v cl) : GTot prop =
  forall (n: nat) (c: cl) (payload: list v) (kf1 kf2: v -> comp_tree v cl).
    (forall (x: v). obs_le_n apply n (kf1 x) (kf2 x)) ==>
    obs_le_n apply n (apply c payload kf1) (apply c payload kf2)

// ------------------------------------------------------------------ //
//  Convergence is closed under stepping, in both directions           //
// ------------------------------------------------------------------ //

(** One transition backwards: a run of `step s` is a run of `s`, one longer. *)
let converges_back
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl {Step? s})
    (x: v)
  : Lemma (requires converges apply (step apply s) x) (ensures converges apply s x)
  = eliminate exists (n: nat). steps apply n (step apply s) == Done x
    returns converges apply s x
    with _.
      assert (steps apply (n + 1) s == steps apply n (step apply s))

(** ... and forwards. *)
let converges_fwd
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl {Step? s})
    (x: v)
  : Lemma (requires converges apply s x) (ensures converges apply (step apply s) x)
  = eliminate exists (n: nat). steps apply n s == Done x
    returns converges apply (step apply s) x
    with _.
      if n = 0 then ()
      else assert (steps apply n s == steps apply (n - 1) (step apply s))

(**
 * **Approximation is a congruence for the left argument of a bind**, with the
 * *same* `g`. One transition of the left run is spent pushing `BindF g`, and
 * the rest is a run of `c1` under a stack both sides share, which is where the
 * hypothesis applies; `obs_le_n_mono` recovers the budget lost to the push.
 *
 * The restriction to a common `g` is not laziness: with different
 * continuations the stacks would differ throughout the left run, and relating
 * them would be the business of `sim`, whose conclusion is an unbounded
 * convergence from which no index survives for a second use of the hypothesis.
 *)
let op_congr_head
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n: nat)
    (c1 c2: comp_tree v cl)
    (g: v -> comp_tree v cl)
  : Lemma (requires obs_le_n apply n c1 c2)
          (ensures obs_le_n apply n (Op c1 g) (Op c2 g))
  = introduce forall (k: stack v cl) (x: v).
      (steps apply n (Step (Op c1 g) k) == Done x ==> converges apply (Step (Op c2 g) k) x)
    with introduce _ ==> _
    with _. begin
      obs_le_n_mono apply n (n - 1) c1 c2;
      assert (steps apply (n - 1) (Step c1 (BindF g :: k)) == Done x);
      converges_back apply (Step (Op c2 g) k) x
    end

// ------------------------------------------------------------------ //
//  How `find_prompt` reacts to a stack being cut in two               //
// ------------------------------------------------------------------ //

(**
 * The two ways a split of the stack shows up in the result of `find_prompt`:
 * either the search ran past a prefix, and that prefix ends up at the bottom of
 * the *captured* segment (`fp_shift`), or the search stopped inside a prefix,
 * and the suffix ends up at the bottom of what is left *below* the prompt
 * (`fp_below`). Naming them keeps the lemma statements free of `match`.
 *)
let fp_shift
    (#v #cl: Type)
    (pre: stack v cl)
    (o: option (stack v cl & cl & stack v cl))
  : option (stack v cl & cl & stack v cl)
  = match o with
    | None -> None
    | Some (cap, c, below) -> Some (pre @ cap, c, below)

let fp_below
    (#v #cl: Type)
    (post: stack v cl)
    (o: option (stack v cl & cl & stack v cl))
  : option (stack v cl & cl & stack v cl)
  = match o with
    | None -> None
    | Some (cap, c, below) -> Some (cap, c, below @ post)

let fp_shift_comp
    (#v #cl: Type)
    (a b: stack v cl)
    (o: option (stack v cl & cl & stack v cl))
  : Lemma (fp_shift a (fp_shift b o) == fp_shift (a @ b) o)
  = match o with
    | None -> ()
    | Some (cap, _, _) -> append_assoc a b cap

let fp_shift_below
    (#v #cl: Type)
    (a p: stack v cl)
    (o: option (stack v cl & cl & stack v cl))
  : Lemma (fp_shift a (fp_below p o) == fp_below p (fp_shift a o))
  = ()

(** `rev` peels a head onto the tail of the reversal. *)
let rev_cons (#a: Type) (hd: a) (l: list a) : Lemma (rev (hd :: l) == rev l @ [hd])
  = rev_acc_rev' l [hd]; rev_rev' l

(** **The accumulator of `find_prompt_aux` is exactly a shift**: the frames
    already walked past are pushed, reversed, onto the bottom of the captured
    segment, which is what returns them in their original order. Every fact
    below about `find_prompt` goes through this. *)
let rec fp_aux_acc
    (#v #cl: Type)
    (eff op: string)
    (soFar k: stack v cl)
  : Lemma (ensures find_prompt_aux eff op soFar k == fp_shift (rev soFar) (find_prompt eff op k))
          (decreases k)
  = match k with
    | [] -> ()
    | hd :: tl ->
      let below () : Lemma (find_prompt_aux eff op soFar k == fp_shift (rev soFar) (find_prompt eff op k)) =
        fp_aux_acc eff op (hd :: soFar) tl;
        fp_aux_acc eff op [hd] tl;
        rev_cons hd soFar;
        fp_shift_comp (rev soFar) [hd] (find_prompt eff op tl)
      in
      (match hd with
        | PromptF hs _ ->
          (match lookup_clause hs eff op with
            | Some _ -> rev_cons hd soFar
            | None -> below ())
        | BindF _ -> below ())

(** **The prompt lies in the upper part**: the search never reaches the lower
    part, which stays where it was, at the bottom of `below`. *)
let rec fp_append_in
    (#v #cl: Type)
    (eff op: string)
    (k1 k2: stack v cl)
  : Lemma (requires handled_in eff op k1)
          (ensures find_prompt eff op (k1 @ k2) == fp_below k2 (find_prompt eff op k1))
          (decreases k1)
  = match k1 with
    | [] -> ()
    | hd :: tl ->
      let below () : Lemma (requires handled_in eff op tl)
                           (ensures find_prompt eff op (k1 @ k2) == fp_below k2 (find_prompt eff op k1)) =
        fp_append_in eff op tl k2;
        fp_aux_acc eff op [hd] (tl @ k2);
        fp_aux_acc eff op [hd] tl;
        fp_shift_below [hd] k2 (find_prompt eff op tl)
      in
      (match hd with
        | PromptF hs _ ->
          (match lookup_clause hs eff op with
            | Some _ -> ()
            | None -> below ())
        | BindF _ -> below ())

(** **The upper part holds no prompt for this action**: the search walks clean
    past it, and the whole of it is captured. *)
let rec fp_append_out
    (#v #cl: Type)
    (eff op: string)
    (k1 k2: stack v cl)
  : Lemma (requires ~(handled_in eff op k1))
          (ensures find_prompt eff op (k1 @ k2) == fp_shift k1 (find_prompt eff op k2))
          (decreases k1)
  = match k1 with
    | [] -> ()
    | hd :: tl ->
      fp_append_out eff op tl k2;
      fp_aux_acc eff op [hd] (tl @ k2);
      fp_shift_comp [hd] tl (find_prompt eff op k2)

// ------------------------------------------------------------------ //
//  The shape of a monad-law redex, as seen by the machine              //
// ------------------------------------------------------------------ //

(**
 * Each of the two hard laws is, once the head constructors have been consumed,
 * a claim about two *stacks*. Right identity leaves the machine comparing
 *
 *     BindF Var :: k        against        k
 *
 * and associativity leaves it comparing
 *
 *     BindF f :: BindF g :: k    against    BindF (fun x -> Op (f x) g) :: k.
 *
 * Both are the same phenomenon: a fixed, prompt-free block of frames `d1`
 * replaced by another such block `d2` inside an otherwise identical stack.
 * `sim` below proves once that such a replacement is unobservable; the laws are
 * its instances.
 *)

(** A block of frames installs no handler. *)
let rec no_prompt (#v #cl: Type) (d: stack v cl) : bool =
  match d with
  | [] -> true
  | f :: r -> BindF? f && no_prompt r

(** Hence the search for a prompt walks straight past it. *)
let rec no_prompt_unhandled
    (#v #cl: Type)
    (eff op: string)
    (d: stack v cl)
  : Lemma (requires no_prompt d) (ensures ~(handled_in eff op d)) (decreases d)
  = match d with
    | [] -> ()
    | _ :: r -> no_prompt_unhandled eff op r

(**
 * **The law itself, as a transition equation.** When a value finally reaches the
 * replaced block, the two machines converge: `i` transitions on the left and `j`
 * on the right land in *the same configuration*, after which the two runs are
 * literally identical.
 *
 * For right identity this is `i = 1`, `j = 0` -- popping `BindF Var` returns the
 * value unchanged. For associativity it is `i = 1`, `j = 2`: on the left `f` is
 * entered with `BindF g` parked below, on the right the composite frame rebuilds
 * `Op (f a) g` and one further transition parks the very same `BindF g`.
 *)
let redex
    (#v #cl: Type)
    (apply: apply_t v cl)
    (i j: nat)
    (d1 d2: stack v cl)
  : GTot prop
  = forall (a: v) (post: stack v cl).
      steps apply i (Step (Var a) (d1 @ post)) == steps apply j (Step (Var a) (d2 @ post))

(** The redex equation is what settles the case where the block is finally met. *)
let redex_converges
    (#v #cl: Type)
    (apply: apply_t v cl)
    (i j: nat)
    (d1 d2: stack v cl)
    (n: nat)
    (post: stack v cl)
    (a x: v)
  : Lemma
      (requires redex apply i j d1 d2 /\
                steps apply n (Step (Var a) (d1 @ post)) == Done x)
      (ensures converges apply (Step (Var a) (d2 @ post)) x)
  = let s1 = Step (Var a) (d1 @ post) in
    let s2 = Step (Var a) (d2 @ post) in
    steps_stable apply n i s1;
    steps_add apply i n s1;
    steps_add apply j n s2;
    assert (steps apply (j + n) s2 == Done x);
    introduce exists (m: nat). steps apply m s2 == Done x
    with (j + n) and ()

// ------------------------------------------------------------------ //
//  The simulation                                                      //
// ------------------------------------------------------------------ //

(**
 * **The delimited continuation `step` hands to a clause**, named -- not for
 * convenience. `step` builds it as the anonymous `fun x -> Resumed captured x`,
 * where `captured` is bound by the `match` on `find_prompt eff op k`, so after
 * elaboration the lambda closes over *the search result itself*. Closure
 * equality is not extensional, so a freshly written `fun x -> Resumed cap x` is
 * a different SMT symbol however provably equal `cap` and `captured` are: any
 * statement about the machine at a `Perform` must spell the continuation
 * exactly as `step` does, which is what this definition is for.
 *
 * The `None` branch is unreachable wherever this is used; it is filled in with
 * `Var` only to keep the definition total and free of a refinement.
 *)
let kont_of (#v #cl: Type) (eff op: string) (k: stack v cl) : v -> comp_tree v cl =
  match find_prompt eff op k with
  | Some (captured, clause, below) -> (fun x -> Resumed captured x)
  | None -> Var

(** ... and its only relevant property: it resumes the captured segment. *)
let kont_of_beta
    (#v #cl: Type)
    (eff op: string)
    (k cap: stack v cl)
    (cls: cl)
    (bel: stack v cl)
  : Lemma (requires find_prompt eff op k == Some (cap, cls, bel))
          (ensures forall (y: v). kont_of eff op k y == Resumed cap y)
  = ()

(**
 * **Feeding a clause two continuations that agree pointwise is unobservable.**
 *
 * Morally this is functional extensionality, which F* does not have for plain
 * arrows. No extra assumption is needed, though: pointwise *equal*
 * continuations are in particular observationally related at every index, so
 * the already-assumed `apply_obs_congr` delivers the conclusion at every index,
 * which is `obs_le`.
 *
 * The situation arises when two runs differ only in a block of frames *below*
 * the handling prompt: they reach the same clause with the same captured
 * segment, but `step` builds the continuation as a closure over the whole
 * `find_prompt` result, and those results differ in their third component.
 *)
let apply_pointwise
    (#v #cl: Type)
    (apply: apply_t v cl)
    (cls: cl)
    (payload: list v)
    (kf1 kf2: v -> comp_tree v cl)
  : Lemma (requires apply_obs_congr apply /\ (forall (y: v). kf1 y == kf2 y))
          (ensures obs_le apply (apply cls payload kf1) (apply cls payload kf2))
  = introduce forall (n: nat). obs_le_n apply n (apply cls payload kf1) (apply cls payload kf2)
    with assert (forall (y: v). obs_le_n apply n (kf1 y) (kf2 y))

(** `step` at a `Perform`, read off a known outcome of the search. *)
let step_perform_found
    (#v #cl: Type)
    (apply: apply_t v cl)
    (eff op: string)
    (payload: list v)
    (k cap: stack v cl)
    (cls: cl)
    (bel: stack v cl)
  : Lemma (requires find_prompt eff op k == Some (cap, cls, bel))
          (ensures step apply (Step (Perform eff op payload) k) ==
                   Step (apply cls payload (kont_of eff op k)) bel)
  = ()

(**
 * **Replacing `d1` by `d2` anywhere in the stack preserves convergence.**
 *
 * Generalised over the frames `pre` above the block and `post` below it,
 * because that is what the induction needs: every transition either pushes a
 * frame onto `pre`, pops one off it, or -- at a `Perform` -- cuts the stack in
 * two, and the block ends up wholly on one side of the cut precisely because it
 * holds no prompt.
 *
 * The induction is on the length `n` of the left-hand run. Five of the six
 * cases are bookkeeping; the one with content is a `Perform` whose handling
 * prompt lies *below* the block, where the block is swallowed into the
 * delimited continuation, the two sides call `apply` on genuinely different
 * arguments, and only `apply_obs_congr` can bridge them -- fed the induction
 * hypothesis two steps down, which is exactly the index it demands.
 *)
let rec sim
    (#v #cl: Type)
    (apply: apply_t v cl)
    (i j: nat)
    (d1 d2: stack v cl)
    (n: nat)
    (pre post: stack v cl)
    (c: comp_tree v cl)
    (x: v)
  : Lemma
      (requires apply_obs_congr apply /\ no_prompt d1 /\ no_prompt d2 /\
                redex apply i j d1 d2 /\
                steps apply n (Step c (pre @ (d1 @ post))) == Done x)
      (ensures converges apply (Step c (pre @ (d2 @ post))) x)
      (decreases %[n; 1])
  = let k1 = pre @ (d1 @ post) in
    let k2 = pre @ (d2 @ post) in
    if n = 0 then ()
    else begin
      assert (steps apply n (Step c k1) == steps apply (n - 1) (step apply (Step c k1)));
      match c with
      | Op c' fn ->
          sim apply i j d1 d2 (n - 1) (BindF fn :: pre) post c' x;
          converges_back apply (Step c k2) x
      | Handle hs r b ->
          sim apply i j d1 d2 (n - 1) (PromptF hs r :: pre) post b x;
          converges_back apply (Step c k2) x
      | Resumed cap y ->
          append_assoc cap pre (d1 @ post);
          append_assoc cap pre (d2 @ post);
          sim apply i j d1 d2 (n - 1) (cap @ pre) post (Var y) x;
          converges_back apply (Step c k2) x
      | Var a ->
          (match pre with
            | [] -> redex_converges apply i j d1 d2 n post a x
            | BindF fn :: pre' ->
                sim apply i j d1 d2 (n - 1) pre' post (fn a) x;
                converges_back apply (Step c k2) x
            | PromptF hs (Some r) :: pre' ->
                sim apply i j d1 d2 (n - 1) pre' post (r a) x;
                converges_back apply (Step c k2) x
            | PromptF hs None :: pre' ->
                sim apply i j d1 d2 (n - 1) pre' post (Var a) x;
                converges_back apply (Step c k2) x)
      | Perform eff op payload ->
          no_prompt_unhandled eff op d1;
          no_prompt_unhandled eff op d2;
          (match find_prompt eff op pre with
            | Some (cap, cls, bel) ->
                // The prompt lies above the block: both machines capture the
                // same segment `cap` and the block stays below the cut. The two
                // continuations are pointwise equal but built as closures over
                // differing search results; `apply_pointwise` bridges the gap.
                fp_append_in eff op pre (d1 @ post);
                fp_append_in eff op pre (d2 @ post);
                step_perform_found apply eff op payload k1 cap cls (bel @ (d1 @ post));
                step_perform_found apply eff op payload k2 cap cls (bel @ (d2 @ post));
                kont_of_beta eff op k1 cap cls (bel @ (d1 @ post));
                kont_of_beta eff op k2 cap cls (bel @ (d2 @ post));
                sim apply i j d1 d2 (n - 1) bel post
                    (apply cls payload (kont_of eff op k1)) x;
                apply_pointwise apply cls payload (kont_of eff op k1) (kont_of eff op k2);
                converges_back apply (Step c k2) x
            | None ->
                fp_append_out eff op pre (d1 @ post);
                fp_append_out eff op pre (d2 @ post);
                fp_append_out eff op d1 post;
                fp_append_out eff op d2 post;
                fp_shift_comp pre d1 (find_prompt eff op post);
                fp_shift_comp pre d2 (find_prompt eff op post);
                (match find_prompt eff op post with
                  | None -> steps_terminal apply (n - 1) (Stuck eff op <: state v cl)
                  | Some (capP, cls, bel) ->
                      append_assoc pre d1 capP;
                      append_assoc pre d2 capP;
                      assert (find_prompt eff op (d1 @ post) == Some (d1 @ capP, cls, bel));
                      assert (find_prompt eff op (d2 @ post) == Some (d2 @ capP, cls, bel));
                      assert (find_prompt eff op k1 == fp_shift pre (find_prompt eff op (d1 @ post)));
                      assert (find_prompt eff op k2 == fp_shift pre (find_prompt eff op (d2 @ post)));
                      assert (find_prompt eff op k1 == Some (pre @ (d1 @ capP), cls, bel));
                      assert (find_prompt eff op k1 == Some ((pre @ d1) @ capP, cls, bel));
                      assert (find_prompt eff op k2 == Some ((pre @ d2) @ capP, cls, bel));
                      step_perform_found apply eff op payload k1 ((pre @ d1) @ capP) cls bel;
                      step_perform_found apply eff op payload k2 ((pre @ d2) @ capP) cls bel;
                      kont_of_beta eff op k1 ((pre @ d1) @ capP) cls bel;
                      kont_of_beta eff op k2 ((pre @ d2) @ capP) cls bel;
                      perform_below apply i j d1 d2 n pre post capP cls bel
                                    (kont_of eff op k1) (kont_of eff op k2) payload x;
                      converges_back apply (Step c k2) x))
    end

(**
 * **The case with content.** The action is handled below the block, so the
 * block is part of what `find_prompt` captures. The two sides therefore call
 * `apply` on continuations differing by exactly the same replacement, one level
 * down inside a `Resumed` node; `apply_obs_congr` turns that into a relation
 * between the clause bodies, and the induction hypothesis at `n - 2` supplies
 * the premise it needs.
 *)
and perform_below
    (#v #cl: Type)
    (apply: apply_t v cl)
    (i j: nat)
    (d1 d2: stack v cl)
    (n: nat)
    (pre post capP: stack v cl)
    (cls: cl)
    (bel: stack v cl)
    (kf1 kf2: v -> comp_tree v cl)
    (payload: list v)
    (x: v)
  : Lemma
      (requires apply_obs_congr apply /\ no_prompt d1 /\ no_prompt d2 /\
                redex apply i j d1 d2 /\ n >= 1 /\
                (forall (y: v). kf1 y == Resumed ((pre @ d1) @ capP) y) /\
                (forall (y: v). kf2 y == Resumed ((pre @ d2) @ capP) y) /\
                steps apply (n - 1) (Step (apply cls payload kf1) bel) == Done x)
      (ensures converges apply (Step (apply cls payload kf2) bel) x)
      (decreases %[n; 0])
  = introduce forall (y: v). obs_le_n apply (n - 1) (kf1 y) (kf2 y)
    with introduce forall (k: stack v cl) (z: v).
           (steps apply (n - 1) (Step (kf1 y) k) == Done z ==>
            converges apply (Step (kf2 y) k) z)
    with introduce _ ==> _
    with _. begin
      append_assoc (pre @ d1) capP k;
      append_assoc pre d1 (capP @ k);
      append_assoc (pre @ d2) capP k;
      append_assoc pre d2 (capP @ k);
      assert (steps apply (n - 1) (Step (kf1 y) k) ==
              steps apply (n - 2) (Step (Var y) (pre @ (d1 @ (capP @ k)))));
      sim apply i j d1 d2 (n - 2) pre (capP @ k) (Var y) z;
      converges_back apply (Step (kf2 y) k) z
    end;
    assert (obs_le_n apply (n - 1) (apply cls payload kf1) (apply cls payload kf2))

// ------------------------------------------------------------------ //
//  The monad laws                                                      //
// ------------------------------------------------------------------ //

(**
 * **Left identity**: `pure a >>= fn  ~  fn a`.
 *
 * The one law that needs no assumption: the extra frame the left side pushes is
 * popped two transitions later, by the value `a` sitting right there, so no
 * operation ever runs while it is on the stack and no captured continuation can
 * tell the two sides apart. The relation is a strict step count -- `n + 2` on
 * the left is `n` on the right -- and both directions follow from that.
 *)
let left_identity
    (#v #cl: Type)
    (apply: apply_t v cl)
    (a: v)
    (fn: v -> comp_tree v cl)
  : Lemma (obs_eq apply (Op (Var a) fn) (fn a))
  = introduce forall (k: stack v cl) (x: v).
      (converges apply (Step (Op (Var a) fn) k) x ==> converges apply (Step (fn a) k) x)
    with introduce _ ==> _
    with _. begin
      converges_fwd apply (Step (Op (Var a) fn) k) x;
      converges_fwd apply (Step (Var a) (BindF fn :: k)) x
    end;
    introduce forall (k: stack v cl) (x: v).
      (converges apply (Step (fn a) k) x ==> converges apply (Step (Op (Var a) fn) k) x)
    with introduce _ ==> _
    with _. begin
      converges_back apply (Step (Var a) (BindF fn :: k)) x;
      converges_back apply (Step (Op (Var a) fn) k) x
    end

(**
 * The redex equation behind right identity: a `BindF` frame holding the return
 * of the monad is popped without doing anything, so one transition on the left
 * is none on the right. The frame's function is a parameter constrained
 * pointwise rather than `Var` outright, so that nothing depends on how F*
 * encodes a constructor used as a function.
 *)
let redex_right
    (#v #cl: Type)
    (apply: apply_t v cl)
    (r: v -> comp_tree v cl)
  : Lemma (requires forall (x: v). r x == Var x)
          (ensures redex apply 1 0 [BindF r] ([] <: stack v cl) /\
                   redex apply 0 1 ([] <: stack v cl) [BindF r])
  = ()

(**
 * **Right identity**: `m >>= pure  ~  m`.
 *
 * Unlike left identity this is neither a step-count relation nor a local fact:
 * the extra `BindF` frame stays on the stack as long as `m` runs, so any
 * operation `m` performs is captured together with it and the clause is handed
 * a continuation the right-hand side does not have. That is precisely the
 * replacement `sim` handles -- `[BindF Var]` against the empty block -- and why
 * the law is stated under `apply_obs_congr`.
 *)
let right_identity
    (#v #cl: Type)
    (apply: apply_t v cl)
    (m: comp_tree v cl)
  : Lemma (requires apply_obs_congr apply)
          (ensures obs_eq apply (Op m (Var #v #cl)) m)
  = let d = [BindF (Var #v #cl)] in
    redex_right apply (Var #v #cl);
    introduce forall (k: stack v cl) (x: v).
      (converges apply (Step (Op m (Var #v #cl)) k) x ==> converges apply (Step m k) x)
    with introduce _ ==> _
    with _. begin
      converges_fwd apply (Step (Op m (Var #v #cl)) k) x;
      eliminate exists (n: nat). steps apply n (Step m (d @ k)) == Done x
      returns converges apply (Step m k) x
      with _. sim apply 1 0 d [] n [] k m x
    end;
    introduce forall (k: stack v cl) (x: v).
      (converges apply (Step m k) x ==> converges apply (Step (Op m (Var #v #cl)) k) x)
    with introduce _ ==> _
    with _. begin
      eliminate exists (n: nat). steps apply n (Step m k) == Done x
      returns converges apply (Step (Op m (Var #v #cl)) k) x
      with _.
        (sim apply 0 1 [] d n [] k m x;
         converges_back apply (Step (Op m (Var #v #cl)) k) x)
    end

(**
 * The redex equation behind associativity: reaching the block with a value `a`,
 * the left side enters `f` with `BindF g` parked below it in one transition,
 * and the right side rebuilds `Op (f a) g` and parks the very same frame in two.
 *)
let redex_assoc
    (#v #cl: Type)
    (apply: apply_t v cl)
    (f: v -> comp_tree v cl)
    (g: v -> comp_tree v cl)
    (h: v -> comp_tree v cl)
  : Lemma (requires forall (x: v). h x == Op (f x) g)
          (ensures redex apply 1 2 [BindF f; BindF g] [BindF h] /\
                   redex apply 2 1 [BindF h] [BindF f; BindF g])
  = ()

(**
 * **Associativity**: `(m >>= f) >>= g  ~  m >>= (fun x -> f x >>= g)`.
 *
 * Two `BindF` frames on the left against one composite frame on the right. As
 * with right identity, `m` runs with the block on the stack, so the two clauses
 * receive different continuations -- hence, again, `apply_obs_congr`.
 *)
let associativity
    (#v #cl: Type)
    (apply: apply_t v cl)
    (m: comp_tree v cl)
    (f g: v -> comp_tree v cl)
  : Lemma (requires apply_obs_congr apply)
          (ensures obs_eq apply (Op (Op m f) g) (Op m (fun x -> Op (f x) g)))
  = let h : v -> comp_tree v cl = fun x -> Op (f x) g in
    let d1 = [BindF f; BindF g] in
    let d2 = [BindF h] in
    redex_assoc apply f g h;
    introduce forall (k: stack v cl) (x: v).
      (converges apply (Step (Op (Op m f) g) k) x ==> converges apply (Step (Op m h) k) x)
    with introduce _ ==> _
    with _. begin
      converges_fwd apply (Step (Op (Op m f) g) k) x;
      converges_fwd apply (Step (Op m f) (BindF g :: k)) x;
      eliminate exists (n: nat). steps apply n (Step m (d1 @ k)) == Done x
      returns converges apply (Step (Op m h) k) x
      with _.
        (sim apply 1 2 d1 d2 n [] k m x;
         converges_back apply (Step (Op m h) k) x)
    end;
    introduce forall (k: stack v cl) (x: v).
      (converges apply (Step (Op m h) k) x ==> converges apply (Step (Op (Op m f) g) k) x)
    with introduce _ ==> _
    with _. begin
      converges_fwd apply (Step (Op m h) k) x;
      eliminate exists (n: nat). steps apply n (Step m (d2 @ k)) == Done x
      returns converges apply (Step (Op (Op m f) g) k) x
      with _.
        (sim apply 2 1 d2 d1 n [] k m x;
         converges_back apply (Step (Op m f) (BindF g :: k)) x;
         converges_back apply (Step (Op (Op m f) g) k) x)
    end

// ------------------------------------------------------------------ //
//  Algebraicity                                                        //
// ------------------------------------------------------------------ //

(**
 * **Operations are algebraic**: `(perform op >>= cont) >>= k  ~  perform op >>= (fun x -> cont x >>= k)`.
 *
 * The usual formulation, "an operation commutes with the continuation",
 *
 *     op(m1, .., mn) >>= k  =  op(m1 >>= k, .., mn >>= k),
 *
 * is not directly expressible here: this encoding has no operation node holding
 * subcomputations. An operation appears as a bare `Perform`, and the only way
 * to put anything after it is to bind, so commuting it with a continuation
 * *is* re-associating a bind whose leftmost leaf is a `Perform` -- which is
 * associativity, specialised.
 *
 * The content is nonetheless real, and is what makes `perform` an *operation*
 * rather than an arbitrary effectful call: whatever the handler does with the
 * captured continuation, the answer does not depend on how much of the
 * surrounding program was already bound to the operation when it was performed.
 * `Handle`, in the next section, fails exactly this test.
 *)
let perform_algebraic
    (#v #cl: Type)
    (apply: apply_t v cl)
    (eff op: string)
    (payload: list v)
    (cont k: v -> comp_tree v cl)
  : Lemma (requires apply_obs_congr apply)
          (ensures obs_eq apply
                     (Op (Op (Perform eff op payload) cont) k)
                     (Op (Perform eff op payload) (fun x -> Op (cont x) k)))
  = associativity apply (Perform eff op payload) cont k

// ------------------------------------------------------------------ //
//  `Handle` is not algebraic                                          //
// ------------------------------------------------------------------ //

(**
 * The claim to refute is that `Handle` behaves like an operation, i.e. that
 *
 *     Op (Handle hs ret m) k   ~   Handle hs ret (Op m k)
 *
 * -- that a handler installed around a computation may be pushed outwards past
 * a bind. It cannot, for the one thing a handler does that an operation does
 * not: it *delimits* continuation capture. On the left, `k` sits below the
 * prompt, so a clause that discards the captured continuation still leaves `k`
 * to run; on the right, `k` sits above the prompt, inside what gets captured,
 * so the very same clause discards it.
 *
 * `apply` is an abstract parameter of the whole development, so a refutation
 * has to instantiate it. Only `LAbort` below is needed for the counterexample;
 * the others are there so that `lapply` is not degenerate, and in particular so
 * that `lapply_obs_congr` is not a statement about a clause that never looks at
 * its continuation.
 *)
noeq
type lcl =
  | LConst : int -> lcl     (* resume with a constant          -- Reader.ask *)
  | LEcho : lcl             (* resume with payload[0]                        *)
  | LAbort : int -> lcl     (* drop the continuation           -- Exc.throw  *)
  | LAddAfter : int -> lcl  (* resume, then add to what comes back           *)

let lapply (c: lcl) (payload: list int) (kf: int -> comp_tree int lcl)
  : comp_tree int lcl
  = match c with
    | LConst n -> kf n
    | LEcho -> (match payload with
                 | y :: _ -> kf y
                 | [] -> Var 0)
    | LAbort n -> Var n
    | LAddAfter n -> Op (kf 0) (fun r -> Var (r + n))

(**
 * **The instance is legitimate**: `lapply` satisfies the very hypothesis the
 * three laws are stated under, so the failure below cannot be blamed on a
 * pathological `apply`.
 *
 * The four clauses cover the ways a clause can treat its continuation, save
 * one. `LAbort` ignores it, so the two results are literally the same term;
 * `LConst` and `LEcho` resume it in head position, where the hypothesis applies
 * as it stands; `LAddAfter` resumes it and then *inspects the value it
 * returns* -- the deep-handler case, and the only one needing an argument,
 * namely `op_congr_head`.
 *
 * Not covered is a clause that resumes the continuation *twice*, as a
 * nondeterminism handler does: the continuation then occurs both in head
 * position and inside a later frame, so the two sides run under differing
 * stacks and `op_congr_head` no longer applies. Such a clause does satisfy the
 * condition -- the budget `n` bounds the whole left run, hence each use of the
 * continuation -- but establishing that needs a congruence relating two stacks
 * that differ pointwise, which this development lacks: `sim` relates stacks
 * differing by a *fixed* block and returns an unbounded convergence, from which
 * no index survives for a second use of the hypothesis. A limitation of the
 * demonstration, not of the condition.
 *)
let lapply_obs_congr () : Lemma (apply_obs_congr lapply)
  = introduce forall (n: nat) (c: lcl) (payload: list int)
                     (kf1 kf2: int -> comp_tree int lcl).
      ((forall (x: int). obs_le_n lapply n (kf1 x) (kf2 x)) ==>
       obs_le_n lapply n (lapply c payload kf1) (lapply c payload kf2))
    with introduce _ ==> _
    with _.
      (match c with
        | LAddAfter m ->
            // The frame `fun r -> Var (r + m)` is not written out: it would be
            // a different closure from the one in `lapply`'s body, which after
            // elaboration closes over `c`. It is read off the result instead,
            // where it is visibly the same on both sides.
            let t1 = lapply c payload kf1 in
            let t2 = lapply c payload kf2 in
            assert (Op? t1 /\ Op? t2);
            assert (Op?.c t1 == kf1 0 /\ Op?.c t2 == kf2 0);
            assert (Op?.fn t1 == Op?.fn t2);
            assert (t1 == Op (kf1 0) (Op?.fn t1));
            assert (t2 == Op (kf2 0) (Op?.fn t1));
            op_congr_head lapply n (kf1 0) (kf2 0) (Op?.fn t1)
        | _ -> ())

(** The handler: one clause, which aborts with `-1`, and no return clause. *)
let lexc : handlers lcl = mk_handlers [("exn", "fail", LAbort (-1))]

(** The operation, and the continuation to be bound to it. *)
let lperform : comp_tree int lcl = Perform "exn" "fail" []
let lcont : int -> comp_tree int lcl = fun x -> Var (x - 1)

(** `handle h m >>= k` -- the handler is *inside*, so `k` survives the abort. *)
let handle_then : comp_tree int lcl = Op (Handle lexc None lperform) lcont

(** `handle h (m >>= k)` -- the handler is *outside*, so `k` is captured and dropped. *)
let then_handle : comp_tree int lcl = Handle lexc None (Op lperform lcont)

(** The two runs, in the empty continuation, give different answers: `-2` where
    the bind survived, `-1` where it was discarded with the captured
    continuation. *)
let handle_then_runs () : Lemma (steps lapply 8 (load handle_then) == Done (-2))
  = assert_norm (steps lapply 8 (load handle_then) == Done (-2))

let then_handle_runs () : Lemma (steps lapply 8 (load then_handle) == Done (-1))
  = assert_norm (steps lapply 8 (load then_handle) == Done (-1))

(**
 * **`Handle` is not algebraic.** The two programs converge, in the same (empty)
 * handler context, to different values; since a run has at most one result
 * (`converges_det`), they cannot be observationally equivalent.
 *
 * Note what is *not* claimed: that no reformulation of `Handle` could be
 * algebraic. The point is about this runtime, and it is the expected one --
 * `handle` is a handler-forming construct, not an operation.
 *)
let handle_not_algebraic () : Lemma (~(obs_eq lapply handle_then then_handle))
  = handle_then_runs ();
    then_handle_runs ();
    let k0 : stack int lcl = [] in
    introduce exists (n: nat). steps lapply n (Step handle_then k0) == Done (-2)
    with 8 and ();
    introduce exists (n: nat). steps lapply n (Step then_handle k0) == Done (-1)
    with 8 and ();
    introduce obs_eq lapply handle_then then_handle ==> False
    with _. begin
      assert (converges lapply (Step handle_then k0) (-2));
      assert (converges lapply (Step then_handle k0) (-2));
      converges_det lapply (Step then_handle k0) (-2) (-1)
    end

(**
 * The same failure, phrased as the negation of the algebraicity schema: there is
 * a handler table, a body and a continuation for which pushing the handler past
 * the bind changes the answer.
 *)
let handle_not_algebraic_exists ()
  : Lemma
      (exists (hs: handlers lcl) (ret: option (int -> comp_tree int lcl))
              (m: comp_tree int lcl) (k: int -> comp_tree int lcl).
          ~(obs_eq lapply (Op (Handle hs ret m) k) (Handle hs ret (Op m k))))
  = handle_not_algebraic ()
