(**
 * The handler table -- the dispatch table a `Handle` installs, abstract.
 *
 * A table maps an action -- that is, pair `(eff, op)` to the clause that handles it.
 * The machine asks it exactly two questions: which clause answers this action (
 * `lookup_clause`, on the hot path of `perform`), and which pairs the table binds at all
 * (`keys`, needed once per `Handle` to extend the evidence environment).
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
 * `Hoop.Runtime.msim` is proved of *every* configuration and may not appeal to
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
 *)
val lookup_clause (#cl: Type) (hs: handlers cl) (eff op: string)
  : Tot (o: option cl { o == assoc_clause (table hs) eff op })

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
 * under `Hoop.Runtime.env_of_stack`, which the solver unfolds constantly.
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
 * where a realisation pays for its representation -- deriving the key cache or
 * building the nested object -- once per table rather than once per `Handle`.
 * The FFI calls it to convert a PureScript handler record into a machine table.
 *)
val mk_handlers (#cl: Type) (l: list (entry cl)) : Tot (hs: handlers cl { table hs == l })

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
 * This is what `Hoop.Runtime.lookup_param_find` spends at every `PromptF` frame,
 * and it is the reason the machine's `ReadP` is a single `Env.lookup` rather
 * than a walk that has to step over levels of the wrong sort.
 *)
val keys_no_var (#cl: Type) (hs: handlers cl) (l: string)
  : Lemma (~(contains (keys hs) (VarKey l)) /\ ~((VarKey l) `mem` keyset_view (keys hs)))

(** **The view of a table built from a list is that list.** *)
val table_mk_handlers (#cl: Type) (l: list (entry cl))
  : Lemma (table (mk_handlers l) == l)

(** **Lookup in a table built from a list is lookup in the list**, the form a
    caller holding a literal table wants. *)
val lookup_clause_mk_handlers (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Lemma (lookup_clause (mk_handlers l) eff op == assoc_clause l eff op)

(**
 * **The keys of a table built from a list are the keys of the list**, as sets.
 *
 * Not as *lists*: `keyset` is abstract precisely so that a realisation may
 * reorder and coalesce the keys -- grouping the operations under their effect is
 * exactly such a reordering -- and `entry_keys` keeps the order and the
 * duplicates of the entry list. What survives is the only thing anything ever
 * asked of it.
 *)
val keys_mk_handlers (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Lemma (contains (keys (mk_handlers l)) (OpKey eff op) <==> ((OpKey eff op) `mem` entry_keys l))

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
