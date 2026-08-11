(**
 * The environment -- the E-component of the CEK machine, in both of its roles.
 *
 * Instead of searching the stack at every `perform`, the machine threads an
 * immutable environment mapping each handled operation to *evidence*: the prompt
 * that handles it, together with the environment that prompt was installed
 * under. `Handle` extends the environment by one level; `perform` reads one key
 * out of it.
 *
 * The same structure holds the prompt-local cells, mapping a label to its value
 * -- which is what E means in a textbook CEK machine, and is why this module is
 * not called `Evidence`. `NewP` extends it by one level and `ReadP` reads one
 * key out of it, by the same two operations. Nothing here distinguishes the two
 * roles: `Hoop.Runtime.Handlers.key` has a constructor for each, so a level
 * binding operations and a level binding a label are told apart by the keys they
 * hold, and this module goes on routing keys to payloads without knowing which
 * sort it is routing. See `Hoop.Runtime.Machine.pd` for why a cell belongs in an
 * environment, which is captured and restored with a continuation, rather than
 * in a store, which is not.
 *
 * The type `env` is abstract and every specification is phrased through the
 * ghost view `levels`. What this interface commits to is only that an
 * environment is a stack of levels, each binding a set of keys to one prompt,
 * innermost first, with lookup returning the innermost binding; a realisation
 * is free to be a prototype chain in which shadowing falls out of property
 * shadowing, and `Hoop.Runtime.Env.fst` discharges it with the obvious list.
 *
 * *Why the payload is a parameter.* A level stores its prompt as an opaque `a`.
 * The machine instantiates it with its own prompt frames but this module never
 * inspects one, so the machine stays free to change what it needs in order to
 * relocate a prompt on the stack -- the frame alone, a frame with an
 * installation depth, a frame with a unique tag -- without touching the
 * environment. Identity of prompts is the machine's business; this module only
 * routes keys to payloads.
 *
 * *Why `below` is here at all.* A handler clause runs in the context the
 * handler was *installed* in, not the one the operation was *performed* in.
 * That context is the environment recorded in the evidence, and it is also the
 * boundary a scoped (higher-order) operation measures against when it asks
 * which prompts are active inside its own handler -- see `prompts_between`.
 *)
module Hoop.Runtime.Env

open FStar.List.Tot

(* The dispatch key comes from the handler tables, this module's only
   dependency: a level binds exactly the keys of the table that installed it, so
   sharing `key` makes `keys_correct` a statement about one type rather than
   about two that agree by hand. The payload stays a parameter -- see above. *)
open Hoop.Runtime.Handlers

(**
 * **One level of an environment**: the keys a single prompt binds, and the
 * prompt itself. `keys` is taken as given, since deriving it needs the shape of
 * a handler table and this module deliberately does not know it.
 *
 * *A flat `list key`, deliberately, and not the abstract
 * `Hoop.Runtime.Handlers.keyset` that `extend` now takes.* A level is a
 * specification object: it is what `levels` yields, hence what `equiv` compares.
 * Were it to carry a keyset, `equiv` would compare keysets by `==` and so
 * distinguish two environments that bind the same keys through differently
 * built keysets -- an equality strictly stronger than the one intended, which
 * `Hoop.Runtime.Machine.mreinstall_equiv` and everything resting on it would silently
 * be asking for. Keeping the *view* here leaves `equiv` exactly as
 * weak as it was and confines the keyset to the realisation, which is where the
 * speed of `contains` is wanted and where nothing is compared.
 *)
type level (a: Type) = {
  keys : list key;
  payload : a;
}

(** **The environment**, abstract: no caller may depend on any structure beyond
    the view below. *)
val env (a: Type u#x) : Type u#x

(**
 * **The specification view**: the levels of an environment, innermost first.
 * Ghost, so no realisation is obliged to compute it -- a prototype chain would
 * have to be walked. This is exactly the amount of structure the abstraction
 * exposes.
 *)
val levels (#a: Type) (w: env a) : GTot (list (level a))

(**
 * **Observational equality of environments**: equal views.
 *
 * Weaker than `==`, and deliberately the only equality this interface commits
 * to: two environments built by different routes can bind the same keys to the
 * same prompts without being the same value, and a correspondence theorem
 * relating an environment to a stack can only pin it down up to its view.
 * `lookup_equiv` is what makes this usable.
 *)
let equiv (#a: Type) (w1 w2: env a) : GTot prop = levels w1 == levels w2

(** **The number of levels**. Concrete rather than ghost: the machine uses it to
    turn an evidence into a count of prompts, which is how the stack split is
    recovered without an identity test (see `Hoop.Runtime.Machine.msplit`). *)
val depth (#a: Type) (w: env a) : Tot (n: nat { n == length (levels w) })

(**
 * **Whether an environment has any level at all.** `depth w = 0` says the same
 * thing but is the wrong thing to *run*: a realisation must produce the whole
 * count even when the question was only whether it is zero, and the machine
 * asks this once for every prompt it leaves, so answering by counting makes
 * unwinding `n` nested handlers cost `n^2`. Every realisation can answer this
 * question without walking anything.
 *)
val is_empty (#a: Type) (w: env a) : Tot (b: bool { b <==> depth w == 0 })

(**
 * **`w'` is an outer environment of `w`**: the levels of `w'` are a suffix of
 * those of `w`, i.e. `w` was reached from `w'` by some sequence of `extend`s.
 *
 * A realisation would test this by pointer identity. The model cannot see
 * identity and does not need to: a suffix is determined by its length, so
 * "walk out until `w'` is reached" becomes "drop the innermost
 * `depth w - depth w'` levels", which is how `prompts_between` is stated.
 *)
let outer_of (#a: Type) (w' w: env a) : GTot prop =
  exists (inner: list (level a)). levels w == inner @ levels w'

(**
 * **Evidence**: the answer to a lookup. `prompt` is the payload of the level
 * that bound the key -- the innermost handler for the operation -- and `below`
 * is the environment that level was pushed onto, the context the handler's
 * clauses run in.
 *
 * `below` is not extra state: `lookup_below_outer` shows it is always an outer
 * environment of the one searched. It is returned rather than recomputed
 * because a realisation has it to hand for free.
 *)
noeq
type evidence (a: Type) = {
  prompt : a;
  below : env a;
}

(**
 * **The model of lookup**, on the view: the innermost level binding `k`, paired
 * with the levels outside it. Shadowing is the `if` taking the first match.
 *
 * *Why `noextract`.* This is the model; `lookup` is what runs, and it answers
 * against the abstract `keyset` with `Handlers.contains` rather than against a
 * list of keys. Nothing calls this at runtime -- extracted, its only caller was
 * itself. It is not merely dead weight, though: it is the one place the
 * extracted runtime used `mem` at a type other than `string`, and a polymorphic
 * `mem` is realised by a *generic* structural comparison. Keeping it off the
 * extracted side is what leaves `runtime/ml/shim/FStar_List_Tot_Base.ml` free of
 * any `mem` at all, and so leaves `caml_compare_val` out of the bundle -- see
 * the note on `mem_string` in `Hoop.Runtime.Handlers`. As with `firstn` below, a
 * `let` in an interface is extracted on its own rather than with its callers, so
 * the qualifier is needed here.
 *)
noextract
let rec find_level (#a: Type) (ls: list (level a)) (k: key)
  : Tot (option (a & list (level a))) (decreases ls)
  = match ls with
    | [] -> None
    | l :: outer -> if k `mem` l.keys then Some (l.payload, outer) else find_level outer k

(**
 * **What `lookup` must return**, named rather than written inline so that no
 * `match` appears in the statement of a lemma. The `below` component is
 * constrained only up to `equiv`, so a realisation may return any environment
 * with the right view.
 *)
let lookup_agrees (#a: Type) (w: env a) (k: key) (o: option (evidence a)) : GTot prop =
  match o with
  | None -> None? (find_level (levels w) k)
  | Some ev ->
      (match find_level (levels w) k with
        | None -> False
        | Some (x, outer) -> ev.prompt == x /\ levels ev.below == outer)

(** **The root environment**: binds nothing. *)
val empty (#a: Type) : (w: env a { levels w == [] })

(**
 * **Installing a prompt**: push one level binding every key of `ks` to `x`.
 * One call per `Handle` -- a single level for the whole handler table, not one
 * per operation, so that leaving the handler pops exactly one level.
 *
 * The keys arrive as an abstract `keyset` and not as a list, because the
 * realisation stores them and answers `contains` against them at every level
 * crossed by every `perform`; that is the loop the abstraction exists for. What
 * lands in the *view* is `keyset_view ks`, so nothing downstream sees the
 * difference.
 *)
val extend (#a: Type) (w: env a) (ks: keyset) (x: a)
  : (w': env a { levels w' == ({ keys = keyset_view ks; payload = x } <: level a) :: levels w })

(**
 * **Leaving a prompt**: drop the innermost level. Pinned down only up to its
 * view, since a realisation returns *an* environment with the right levels and
 * nothing here may depend on which one. Stated as an existential rather than
 * with `Cons?.tl` so that no projector has to be discharged against an abstract
 * `levels`.
 *)
val outer (#a: Type) (w: env a { depth w > 0 })
  : (w': env a { exists (l: level a). levels w == l :: levels w' })

(** **Leaving a prompt undoes installing it.** *)
val outer_extend (#a: Type) (w: env a) (ks: keyset) (x: a)
  : Lemma (depth (extend w ks x) > 0 /\ outer (extend w ks x) `equiv` w)

(** **The hot path**: the evidence for `k`, or `None` if no level binds it. This
    replaces the linear scan of `Hoop.Runtime.Semantics.find_prompt`; that it
    answers the same question is `Hoop.Runtime.Machine.lookup_find`. *)
val lookup (#a: Type) (w: env a) (k: key)
  : Tot (o: option (evidence a) { lookup_agrees w k o })

(* ------------------------------------------------------------------ *)
(*  Scoped effects: the prompts between two environments               *)
(* ------------------------------------------------------------------ *)

(**
 * **The first `n` elements**, total on a possibly-negative `n` so that it may
 * be applied to a difference of depths without that difference having to be
 * shown non-negative first.
 *
 * *Why `noextract`.* That possibly-negative `n` is the only integer here that
 * is not a natural number, and the extracted runtime is built on the assumption
 * that there is no such thing: `runtime/ml/shim/Prims.ml` realises `Prims.int`
 * as a machine integer with a check on every subtraction, and that check
 * rejects exactly the arguments this function is total on. Keeping it off the
 * extracted side is the precondition of the shim being a faithful realisation,
 * not tidiness. A `let` in an interface is extracted on its own rather than
 * with its callers, so the qualifier is needed here as well as on
 * `prompts_between` below.
 *)
noextract
let rec firstn (#a: Type) (n: int) (l: list a) : Tot (list a) (decreases l) =
  if n <= 0 then []
  else match l with
       | [] -> []
       | x :: tl -> x :: firstn (n - 1) tl

(** **The prompts of the levels of `w` that lie inside `below`**, outermost
    first. The specification of `prompts_between`. *)
let inner_payloads (#a: Type) (w: env a) (below: env a) : GTot (list a) =
  rev (map (fun (l: level a) -> l.payload) (firstn (depth w - depth below) (levels w)))

(**
 * **The prompts active in `w` and installed inside `below`**, outermost first.
 *
 * Needed by scoped (higher-order) operations, which reinstall the handlers that
 * were active where the operation was performed. Those come from the
 * *environment* at the perform site, not from the captured stack frames: the
 * two differ exactly when a tail-resumptive clause body is in flight, and a
 * scope must not see a handler that the clause body itself cannot see.
 *
 * The precondition is what `lookup_below_outer` supplies for an evidence
 * obtained from `w`. `noextract` for as long as no transition calls it:
 * extracting it would carry `firstn`'s signed arithmetic into the runtime for
 * nothing -- see there.
 *)
noextract
val prompts_between (#a: Type) (w: env a) (below: env a)
  : Pure (list a)
      (requires below `outer_of` w)
      (ensures fun r -> r == inner_payloads w below)

(* ------------------------------------------------------------------ *)
(*  Derived facts                                                      *)
(*                                                                     *)
(*  Everything below follows from the refinements above; they are named *)
(*  so that callers reason with lemmas rather than by unfolding         *)
(*  `find_level` under an abstract `levels`.                            *)
(* ------------------------------------------------------------------ *)

(** **The root binds nothing.** *)
val lookup_empty (#a: Type) (k: key)
  : Lemma (lookup (empty #a) k == None)

(** **Lookup cannot tell equivalent environments apart**: the congruence that
    makes `equiv` a usable equality. *)
val lookup_equiv (#a: Type) (w1 w2: env a) (k: key)
  : Lemma
      (requires w1 `equiv` w2)
      (ensures
        (match lookup w1 k, lookup w2 k with
          | None, None -> True
          | Some ev1, Some ev2 -> ev1.prompt == ev2.prompt /\ ev1.below `equiv` ev2.below
          | _ -> False))

(** **A freshly installed prompt shadows**: a key of the new table resolves to
    the new prompt, and the evidence's `below` is the environment it was
    installed under. *)
val lookup_extend_hit (#a: Type) (w: env a) (ks: keyset) (x: a) (k: key)
  : Lemma
      (requires k `mem` keyset_view ks)
      (ensures
        (match lookup (extend w ks x) k with
          | None -> False
          | Some ev -> ev.prompt == x /\ ev.below `equiv` w))

(** **Installing a prompt disturbs nothing else**: a key the new table does not
    bind resolves exactly as before. *)
val lookup_extend_miss (#a: Type) (w: env a) (ks: keyset) (x: a) (k: key)
  : Lemma
      (requires ~(k `mem` keyset_view ks))
      (ensures
        (match lookup (extend w ks x) k, lookup w k with
          | None, None -> True
          | Some ev1, Some ev2 -> ev1.prompt == ev2.prompt /\ ev1.below `equiv` ev2.below
          | _ -> False))

(** **The environment below an evidence is an outer environment**, strictly
    shallower. This is what lets `prompts_between` be stated without any notion
    of object identity. *)
val lookup_below_outer (#a: Type) (w: env a) (k: key)
  : Lemma
      (requires Some? (lookup w k))
      (ensures
        (let ev = Some?.v (lookup w k) in
          ev.below `outer_of` w /\ depth ev.below < depth w))

(** **`outer_of` is reflexive**, so that a scope opened directly at a handler
    asks for the prompts between an environment and itself, and gets none. *)
val outer_of_refl (#a: Type) (w: env a)
  : Lemma (w `outer_of` w)

(** **`outer_of` is transitive**, which is what makes a chain of nested scopes
    measurable against a single outer boundary. *)
val outer_of_trans (#a: Type) (w1 w2 w3: env a)
  : Lemma
      (requires w1 `outer_of` w2 /\ w2 `outer_of` w3)
      (ensures w1 `outer_of` w3)

(** **Extending deepens by one.** *)
val depth_extend (#a: Type) (w: env a) (ks: keyset) (x: a)
  : Lemma (depth (extend w ks x) == depth w + 1)
