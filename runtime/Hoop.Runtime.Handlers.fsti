(**
 * The handler table -- the dispatch table a `Handle` installs, abstract.
 *
 * A table maps an action -- that is, pair `(eff, op)` to the clause that handles it.
 * The machine asks it three questions: which clause answers this action (
 * `lookup_clause`, on the hot path of `perform`), which pairs the table binds at all
 * (`keys`, needed once per `Handle` to extend the evidence environment), and --
 * off the hot path, where the answer decides which interpreter a clause is
 * unwrapped to -- that same clause together with its kind (`lookup_handler`).
 * Nothing else about a table is ever inspected, so the type is abstract and every
 * specification below is phrased through the ghost view `table` -- as `Hoop.Runtime.Env`
 * is phrased through `levels`.
 *
 * Abstraction buys two things. `keys` may be a *computable projection*, so a
 * realisation is free to derive the keyset once when the table is built and
 * hand it back here; a ghost function of the table's contents could not express
 * that, and the environment demands the whole keyset at every `Handle` while a
 * closure-capturing handler such as `catch` builds a fresh table at every call.
 * And `lookup_clause` is pinned to a specification rather than to a linear
 * scan, so a realisation keeping a nested object and answering `hs[eff][op]` is
 * equally admissible. `Hoop.Runtime.Handlers.fst` discharges the interface with
 * the flat entry list beside a copy of it grouped by effect, which is that
 * nested object in list form.
 *
 * *The `u#a` on the `val` below is load-bearing.* A `val` has no body, so
 * without it F* generalises argument and result universes independently, and
 * two things break. The realisation, a refinement of a record over `cl`, no
 * longer has the declared type; and `Hoop.Runtime.Syntax.comp_tree` cannot be
 * formed at all, since its `Handle` node carries a `handlers cl` field and an
 * inductive must live at least as high as every field. Neither failure names a
 * universe intelligibly -- the second reports `Failed to solve universe
 * inequalities for inductives`, and dropping the annotation from the definition
 * too downgrades the first to `Expected type Type ... has type Type`. None of
 * this arose while `handlers cl` was the transparent `list (entry cl)`: F* saw
 * for itself that a list lives where its elements do.
 *
 * The other annotations (`entry` here, `htable` and `handlers` in the `.fst`)
 * are each inferable from their bodies and are written out only to keep the
 * constraint visible everywhere the type is named.
 *)
module Hoop.Runtime.Handlers

open FStar.List.Tot

(**
 * **A name the evidence environment binds**, in either of its two roles.
 *
 * Declared here, where the clauses are, and taken from here by everything else
 * keyed by a name -- the evidence environment included, whose levels bind
 * precisely the keys of the table, or of the cell, that installed them. Two
 * agreeing definitions in two modules would leave `keys_correct` relating types
 * that merely happen to coincide; one definition makes the relation structural.
 *
 * *Why two constructors and not a pair of strings.* `Hoop.Runtime.Env` is the
 * E of the machine and it now plays both of E's roles: it maps each handled
 * operation to the prompt that handles it -- a *handler context* -- and each
 * prompt-local cell to its value, which is the `label -> value` map the letter
 * E was named for. One environment, therefore two sorts of name, and they must
 * not collide: a handler table is built from an arbitrary association list, so
 * nothing stops one from declaring an operation under the reserved effect name
 * `Hoop.Runtime.Semantics.var_eff`, and were a cell keyed by the *pair*
 * `(var_eff, l)` such a table would shadow the cell -- or be shadowed by it --
 * and the environment would stop answering what the reference machine's stack
 * search answers. `Hoop.Runtime.WellScopedness` rules that program out, but
 * `Hoop.Runtime.Machine.msim` is proved of *every* configuration and may not appeal to
 * it. Making the two sorts disjoint constructors settles it in the type: a
 * `VarKey` is unreachable from any `mk_handlers`, which is `keys_no_var`.
 *
 * A realisation with string-keyed objects would encode a key into one string,
 * say `"<strlen eff>:<eff><op>"` for an operation and `"%<l>"` for a cell. That
 * such an encoding is injective cannot be proved here -- it needs
 * `string_of_int` to be injective and never to produce a `':'`, and
 * `FStar.String` says nothing about it -- so the model keeps the constructors
 * rather than assume it, leaving the encoding an optimisation inside the
 * realisation, to be covered by differential testing.
 *)
type key =
  | OpKey : eff:string -> op:string -> key
  | VarKey : label:string -> key

(** **One entry of a table**: a key together with the clause it selects. A table
    binds operations only, so the entry names one with its two components rather
    than carrying a `key` that could be a `VarKey`. *)
let entry (cl: Type u#a) : Type u#a = string & string & cl

(* ------------------------------------------------------------------ *)
(*  What kind of clause an entry holds                                 *)
(* ------------------------------------------------------------------ *)

(**
 * **The kind of a clause, as a flat enumeration** -- deliberately independent of
 * `cl`.
 *
 * A table is polymorphic in the clause type and therefore cannot see a tag:
 * `Hoop.Runtime.Machine.clause`'s `Full` / `Fast` constructors typecheck only where `cl`
 * is `clause cl0`, which is `Hoop.Runtime.Machine` and nowhere else. Anything that has
 * to *name* a kind while staying `cl`-polymorphic -- scoped dispatch deciding
 * which interpreter to unwrap to, a boundary rejection reporting the kind it
 * actually found -- needs a type it can mention, and this is it. The bridge
 * between the two is a classifier taken once, at `mk_handlers`, in the layer
 * that owns the tags.
 *
 * **`blocking_effects` below tests "not `KFast`", never "is `KFull`".** A scoped
 * clause blocks a borrow for the reason a full one does -- its canonical type
 * mentions the answer type, so the stored representation cannot be reused at the
 * scope's -- and stating the test negatively is what lets it say so without a
 * second arm to keep in step with this type.
 *)
type clause_kind =
  | KFull
  | KFast
  | KScoped

(**
 * **A clause together with its kind**, the shape a lookup that needs both hands
 * back.
 *
 * The point of the record is that the pairing is *structural*: a caller holding
 * one cannot be looking at a clause from one table and a kind from another, nor
 * at a kind recomputed by a classifier that has since drifted from the one the
 * table was built with. That is worth more than the second scan it saves.
 *)
type found_clause (cl: Type u#a) : Type u#a = {
  body : cl;
  kind : clause_kind;
}

(** **The classifier, applied.** Named rather than written as a lambda at each
    use, so that the construction refinement on `mk_handlers` and every proof
    that reads it speak of one SMT symbol. *)
let found_of (#cl: Type) (classify: cl -> clause_kind) (c: cl) : found_clause cl =
  { body = c; kind = classify c }

(** **`option`'s map.** `unfold` so that the specifications below reduce to a
    `match` the solver can see through rather than to an opaque application. *)
unfold
let map_opt (#a #b: Type) (f: a -> b) (o: option a) : option b =
  match o with
  | None -> None
  | Some x -> Some (f x)

(**
 * **First-match association lookup**, the specification of `lookup_clause`.
 *
 * "First match" is not incidental: a table written with two clauses for the
 * same operation must behave as if only the earlier one were there, and the
 * whole interface is pinned to this function, so every realisation shadows the
 * same way.
 *)
let rec assoc_clause (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Tot (option cl) (decreases l)
  = match l with
    | [] -> None
    | (e, o, c) :: rest -> if e = eff && o = op then Some c else assoc_clause rest eff op

(** **The keys of an association list**: the specification of `keys`, not the
    way any particular realisation computes it. *)
let rec entry_keys (#cl: Type) (l: list (entry cl)) : Tot (list key) (decreases l) =
  match l with
  | [] -> []
  | (eff, op, _) :: rest -> OpKey eff op :: entry_keys rest

(* ------------------------------------------------------------------ *)
(*  Key sets                                                           *)
(* ------------------------------------------------------------------ *)

(**
 * **A set of dispatch keys**, abstract, and *independent of the clause type*.
 *
 * The environment stores one of these per installed prompt and asks it a single
 * question -- does it bind this key? -- once per level crossed on every
 * `perform`. That is the hot loop of the whole runtime, so the question is put
 * to an abstract type rather than to a `list key`: a flat list answers a miss in
 * as many comparisons as the handler declares operations, while a realisation
 * grouping the operations under their effect answers the same miss in one.
 *
 * `Type0` and not a function of `cl` on purpose. A keyset is what a handler
 * table hands the environment, and the environment knows nothing of clauses;
 * were the type to mention `cl`, `Hoop.Runtime.Env` would have to be
 * parameterised by it.
 *)
val keyset : Type0

(**
 * **The specification view of a keyset**: the keys it holds, as a list. Ghost,
 * so no realisation is obliged to flatten itself; it exists so that everything
 * *about* keysets can go on being said with `mem` on a plain list, which is what
 * keeps `Hoop.Runtime.Env.level` -- and hence `Hoop.Runtime.Env.equiv` -- free
 * of this abstraction. See the header of `Hoop.Runtime.Env` on why that matters.
 *)
val keyset_view (s: keyset) : GTot (list key)

(** **Membership**, computed: the one question the environment asks, and the
    reason the type is abstract. Pinned to the view, so a realisation may answer
    it however it likes. *)
val contains (s: keyset) (k: key) : Tot (b: bool { b <==> k `mem` keyset_view s })

(**
 * **The keyset of a prompt-local cell**: the one name a `ParamF` level binds.
 *
 * A cell installs a level of the environment exactly as a handler table does --
 * that is what makes E hold `label -> value` alongside `operation -> prompt` --
 * and a level is built from a `keyset`, which is abstract, so the singleton
 * cannot be written at the call site. Hence this.
 *
 * It is here rather than in `Hoop.Runtime.Env` because `keyset` is realised
 * here and its realisation is what a singleton has to be built in; and it takes
 * the label rather than a `key` so that the sort is fixed by the type -- there
 * is no way to ask for a cell level that binds an operation.
 *)
val var_keyset (l: string) : Tot (s: keyset { keyset_view s == [VarKey l] })

(** **The handler table**, abstract. The `u#a` is the one annotation in the pair
    of files that cannot be dropped -- see the module header. *)
val handlers (cl: Type u#a) : Type u#a

(**
 * **The specification view**: the entries of a table, in the order that decides
 * shadowing. Ghost, so no realisation is obliged to produce it -- a nested
 * object would have to flatten itself, in an order it does not actually keep.
 * This is exactly the amount of structure the abstraction exposes.
 *)
val table (#cl: Type) (hs: handlers cl) : GTot (list (entry cl))

(**
 * **The hot path**: the clause handling `(eff, op)`, or `None` if the table
 * does not bind it.
 *
 * A refinement rather than a separate lemma because `lookup_clause` occurs
 * inside `Hoop.Runtime.WellScopedness.handler_ok` and inside `handles`, both
 * unfolded by the solver on nearly every query, and a fact carried by the type
 * never has to be recalled.
 *
 * *This is a primitive of the interface, and it must stay one.* Reading it as
 * `map_opt (fun f -> f.body) (lookup_handler hs eff op)` would be shorter by a
 * `val`, by a realisation and by the coherence lemma below -- and it would put
 * an allocation back on the hot loop. `Hoop.Runtime.Machine.mstep`'s ordinary `Perform`
 * rule reaches its clause through this function and dispatches a `Fast` clause
 * without ever building a `found_clause`; that record is what the scoped path
 * pays for, and the scoped path walks the stack anyway. Removing one
 * polymorphic string comparison from this loop was once worth about 12% of a
 * State-heavy benchmark, which is the scale a needless record per `perform`
 * would be measured against.
 *
 * The two are therefore realised independently and related by
 * `lookup_handler_agrees`. A caller loses nothing: what a single combined lookup
 * would have given definitionally is available here as one lemma call.
 *)
val lookup_clause (#cl: Type) (hs: handlers cl) (eff op: string)
  : Tot (o: option cl { o == assoc_clause (table hs) eff op })

(**
 * **The same lookup, with the kind**: for the callers that need to know what
 * sort of clause they found before they can act on it -- scoped dispatch
 * choosing an interpreter, a boundary rejection naming what it got, and
 * `blocking_effects` below.
 *
 * Not refined against `table`, because there is nothing to say there that
 * `lookup_clause`'s refinement and `lookup_handler_agrees` do not already say:
 * the *kind* half is fixed by the construction refinement on `mk_handlers`, and
 * only there. The kinds a table reports are exactly the kinds the classifier it
 * was built with assigns, and no abstract `classify_of : handlers cl -> cl ->
 * clause_kind` has to be carried around for that to be stated.
 *)
val lookup_handler (#cl: Type) (hs: handlers cl) (eff op: string)
  : Tot (option (found_clause cl))

(** **The two lookups agree on the clause.** The coherence that makes
    `lookup_handler` a refinement of `lookup_clause` rather than a second,
    independently fallible search of the same table. *)
val lookup_handler_agrees (#cl: Type) (hs: handlers cl) (eff op: string)
  : Lemma (map_opt (fun (f: found_clause cl) -> f.body) (lookup_handler hs eff op)
             == lookup_clause hs eff op)

let clause_memP (#cl: Type) (c:cl) (hs: handlers cl)
  : prop
  = exists eff op. lookup_clause hs eff op == Some c

(**
 * **The keys a table binds**, cached: concrete rather than ghost, which is the
 * point of the abstraction. A realisation is expected to have derived this
 * keyset once, when the table was built -- this must be a field read, since the
 * environment demands it at every `Handle` and a closure-capturing handler such
 * as `catch` builds a fresh table at every call.
 *
 * The refinement is the bridge to the environment -- the keys are *exactly* the
 * operations the table handles, so "the environment binds this key" and "this
 * table has a clause for this operation" are interchangeable. It is stated
 * twice, once through `contains` and once through the view, because callers
 * come from both sides: the machine runs `contains`, while every specification
 * downstream (`Hoop.Runtime.Env.find_level`, `level_well_keyed`) speaks of `mem`
 * on the view.
 *
 * The third and fourth conjuncts are the disjointness of the two sorts, read off
 * the only constructor a table has: *no* table binds a cell name, whatever
 * association list it was built from. That is what makes a prompt level
 * transparent to a cell lookup, and it is stated as a refinement rather than
 * only as `keys_no_var` for the same reason as the others -- `keys` occurs
 * under `Hoop.Runtime.Machine.env_of_stack`, which the solver unfolds constantly.
 *)
val keys (#cl: Type) (hs: handlers cl)
  : Tot (ks: keyset {
      (forall (eff op: string). contains ks (OpKey eff op) <==> Some? (lookup_clause hs eff op)) /\
      (forall (eff op: string).
        ((OpKey eff op) `mem` keyset_view ks) <==> Some? (lookup_clause hs eff op)) /\
      (forall (l: string). ~(contains ks (VarKey l))) /\
      (forall (l: string). ~((VarKey l) `mem` keyset_view ks))
    })

(**
 * **Building a table from an association list**: the only constructor, and
 * where a realisation pays for its representation -- deriving the key cache,
 * building the nested object, classifying the clauses -- once per table rather
 * than once per `Handle`.
 *
 * *Why the classifier is an argument.* It is the one thing a `cl`-polymorphic
 * table cannot compute for itself, and the one thing that must not be trusted
 * from the boundary: a `mk_handlers` reachable from the FFI with a classifier of
 * the FFI's choosing is a trusted input in functional form -- `fun _ -> KFast`
 * would declare every table borrowable, silently. So the classifier is taken
 * here, pinned by the refinement below rather than believed, and fixed on the
 * shipping path by `Hoop.Runtime.Machine.mk_runtime_handlers`, which is the only
 * `mk_handlers` caller the boundary is allowed to name.
 *
 * The refinement fixes all three views of the result: the ghost view, the hot
 * lookup, and the kinds. Only the third mentions `classify`, and it is the only
 * place in the development that does -- everything else about kinds, including
 * `blocking_effects`, is derived from `lookup_handler`.
 *)
val mk_handlers (#cl: Type) (classify: cl -> clause_kind) (l: list (entry cl))
  : Tot (hs: handlers cl {
      table hs == l /\
      (forall (eff op: string). lookup_clause hs eff op == assoc_clause l eff op) /\
      (forall (eff op: string).
        lookup_handler hs eff op == map_opt (found_of classify) (assoc_clause l eff op))
    })

(**
 * **The effects that stand in the way of a borrow**, as a set.
 *
 * A prompt is borrowable -- reinstallable inside a scope without
 * re-instantiation -- exactly when every clause it can dispatch is `KFast`;
 * see the scoped-effects design note on why that is a statement about reuse of
 * the stored representation rather than about tail-resumptiveness. What a
 * failure has to report is *which* handlers blocked, so what the interface
 * offers is the list of offending effect labels, and the boolean is derived
 * from it -- `borrowable` below is a match on this list, not a second answer.
 * A boolean stored beside a list would be one more thing that can disagree
 * with it.
 *
 * *An abstract projection computed on demand, and not -- unlike `keys` -- a
 * cache.* That is the initial realisation, and it stands until `Weave` provides
 * a real access pattern and a benchmark. Caching it at `mk_handlers` time would
 * put a walk on every `Handle` -- the operation
 * `benchmarks/src/Benchmarks/CatchInstall.purs` measures, and one a
 * closure-capturing `catch` pays on every call -- to precompute an answer
 * nothing asks for yet. If `Weave` turns out to be frequent, the same table's
 * answer would be recomputed repeatedly and the trade reverses; the refinement
 * is identical either way, so this can become a field with nothing downstream
 * to revisit.
 *
 * *Stated through `lookup_handler` rather than through the entries.* For a table
 * whose entry list binds the same operation twice, this judges only the entry
 * that would actually be dispatched: a shadowed `Full` clause is invisible to
 * `lookup_clause`, to `clause_memP` and hence to
 * `Hoop.Runtime.WellScopedness.handler_ok`, so it has no business blocking a
 * borrow either.
 *
 * Pinned **as a set**, exactly as `keys` is, so a realisation walking the table
 * by effect group may report the labels in any order and need not repeat one.
 *)
val blocking_effects (#cl: Type) (hs: handlers cl)
  : Tot (l: list string {
      forall (eff: string). eff `mem` l <==>
        (exists (op: string) (found: found_clause cl).
          lookup_handler hs eff op == Some found /\ found.kind =!= KFast)
    })

(** **Borrowability**, derived rather than stored: nothing blocks.
    `Nil? (blocking_effects hs)` is what this says; it is written as the match
    because the recognizer extracts to `Prims.uu___is_Nil`, which
    `runtime/ml/shim/Prims.ml` does not realise -- and the shim exists to stay
    small. *)
let borrowable (#cl: Type) (hs: handlers cl) : bool =
  match blocking_effects hs with
  | [] -> true
  | _ -> false

(* ------------------------------------------------------------------ *)
(*  Derived facts                                                      *)
(*                                                                     *)
(*  Everything below follows from the refinements above; they are named *)
(*  so that callers may reason with lemmas rather than by relying on a  *)
(*  refinement being unfolded at the right moment.                      *)
(* ------------------------------------------------------------------ *)

(** **Lookup is association lookup on the view.** *)
val lookup_clause_spec (#cl: Type) (hs: handlers cl) (eff op: string)
  : Lemma (lookup_clause hs eff op == assoc_clause (table hs) eff op)

(** **The keys are exactly the handled operations.** Stated on the view, which
    is the side every specification downstream is written in. *)
val keys_correct (#cl: Type) (hs: handlers cl) (eff op: string)
  : Lemma (((OpKey eff op) `mem` keyset_view (keys hs)) <==> Some? (lookup_clause hs eff op))

(**
 * **No handler table binds a cell.** The disjointness of the environment's two
 * sorts of name, in the form a caller wants it: a prompt level is transparent to
 * the lookup of a cell, whatever operations its table happens to declare.
 *
 * This is what `Hoop.Runtime.Machine.lookup_param_find` spends at every `PromptF` frame,
 * and it is the reason the machine's `ReadP` is a single `Env.lookup` rather
 * than a walk that has to step over levels of the wrong sort.
 *)
val keys_no_var (#cl: Type) (hs: handlers cl) (l: string)
  : Lemma (~(contains (keys hs) (VarKey l)) /\ ~((VarKey l) `mem` keyset_view (keys hs)))

(** **The view of a table built from a list is that list.** *)
val table_mk_handlers (#cl: Type) (classify: cl -> clause_kind) (l: list (entry cl))
  : Lemma (table (mk_handlers classify l) == l)

(** **Lookup in a table built from a list is lookup in the list**, the form a
    caller holding a literal table wants. *)
val lookup_clause_mk_handlers (#cl: Type) (classify: cl -> clause_kind) (l: list (entry cl))
    (eff op: string)
  : Lemma (lookup_clause (mk_handlers classify l) eff op == assoc_clause l eff op)

(** **... and the kind it reports is the one the classifier assigns.** The
    `lookup_handler` counterpart of the above, in the same caller-facing form. *)
val lookup_handler_mk_handlers (#cl: Type) (classify: cl -> clause_kind) (l: list (entry cl))
    (eff op: string)
  : Lemma (lookup_handler (mk_handlers classify l) eff op
             == map_opt (found_of classify) (assoc_clause l eff op))

(**
 * **The keys of a table built from a list are the keys of the list**, as sets.
 *
 * Not as *lists*: `keyset` is abstract precisely so that a realisation may
 * reorder and coalesce the keys -- grouping the operations under their effect is
 * exactly such a reordering -- and `entry_keys` keeps the order and the
 * duplicates of the entry list. What survives is the only thing anything ever
 * asked of it.
 *)
val keys_mk_handlers (#cl: Type) (classify: cl -> clause_kind) (l: list (entry cl))
    (eff op: string)
  : Lemma (contains (keys (mk_handlers classify l)) (OpKey eff op)
             <==> ((OpKey eff op) `mem` entry_keys l))

(** **Association lookup never forges a clause.** The soundness half of
    `Hoop.Runtime.Metatheory.lookup_clause_memP`, stated on the model because
    that is where the induction lives. *)
val assoc_clause_memP (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Lemma
      (requires Some? (assoc_clause l eff op))
      (ensures memP (eff, op, Some?.v (assoc_clause l eff op)) l)

(** **Association lookup never misses a clause.** The completeness half of
    `Hoop.Runtime.Metatheory.lookup_clause_none`. *)
val assoc_clause_none (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Lemma
      (requires None? (assoc_clause l eff op))
      (ensures forall (c: cl). ~(memP (eff, op, c) l))
