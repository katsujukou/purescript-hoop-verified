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
 * realisation is free to derive the key list once when the table is built and
 * hand it back here; a ghost function of the table's contents could not express
 * that, and the environment demands the whole list at every `Handle` while a
 * closure-capturing handler such as `catch` builds a fresh table at every call.
 * And `lookup_clause` is pinned to a specification rather than to a linear
 * scan, so a realisation keeping a nested object and answering `hs[eff][op]` is
 * equally admissible. `Hoop.Runtime.Handlers.fst` discharges the interface with
 * an association list plus its derived keys.
 *
 * *The `u#a` on the `val` below is load-bearing.* A `val` has no body, so
 * without it F* generalises argument and result universes independently, and
 * two things break. The realisation, a refinement of a record over `cl`, no
 * longer has the declared type; and `Hoop.Runtime.comp_tree` cannot be formed
 * at all, since its `Handle` node carries a `handlers cl` field and an
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

(** **A dispatch key**: the pair naming an operation, as `Hoop.Runtime.Env`
    keys its levels. *)
let key : eqtype = string & string

(** **One entry of a table**: a key together with the clause it selects. *)
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
  | (eff, op, _) :: rest -> (eff, op) :: entry_keys rest

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
 * inside `Hoop.Runtime.handler_ok` and inside `handles`, both unfolded by the
 * solver on nearly every query, and a fact carried by the type never has to be
 * recalled.
 *)
val lookup_clause (#cl: Type) (hs: handlers cl) (eff op: string)
  : Tot (o: option cl { o == assoc_clause (table hs) eff op })

(**
 * **The keys a table binds**, cached: concrete rather than ghost, which is the
 * point of the abstraction. A realisation is expected to have derived this list
 * once, when the table was built.
 *
 * The refinement is the bridge to the environment -- the keys are *exactly* the
 * operations the table handles, so "the environment binds this key" and "this
 * table has a clause for this operation" are interchangeable.
 *)
val keys (#cl: Type) (hs: handlers cl)
  : Tot (ks: list key {
      forall (eff op: string). ((eff, op) `mem` ks) <==> Some? (lookup_clause hs eff op)
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

(** **The keys are exactly the handled operations.** *)
val keys_correct (#cl: Type) (hs: handlers cl) (eff op: string)
  : Lemma (((eff, op) `mem` keys hs) <==> Some? (lookup_clause hs eff op))

(** **The view of a table built from a list is that list.** *)
val table_mk_handlers (#cl: Type) (l: list (entry cl))
  : Lemma (table (mk_handlers l) == l)

(** **Lookup in a table built from a list is lookup in the list**, the form a
    caller holding a literal table wants. *)
val lookup_clause_mk_handlers (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Lemma (lookup_clause (mk_handlers l) eff op == assoc_clause l eff op)

(** **The keys of a table built from a list are the keys of the list.** An
    equality of *lists*, not merely of the sets they denote, so that a caller
    can reduce the reference realisation's cache away. *)
val keys_mk_handlers (#cl: Type) (l: list (entry cl))
  : Lemma (keys (mk_handlers l) == entry_keys l)

(** **Association lookup never forges a clause.** The soundness half of
    `Hoop.Runtime.Properties.lookup_clause_memP`, stated on the model because
    that is where the induction lives. *)
val assoc_clause_memP (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Lemma
      (requires Some? (assoc_clause l eff op))
      (ensures memP (eff, op, Some?.v (assoc_clause l eff op)) l)

(** **Association lookup never misses a clause.** The completeness half of
    `Hoop.Runtime.Properties.lookup_clause_none`. *)
val assoc_clause_none (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Lemma
      (requires None? (assoc_clause l eff op))
      (ensures forall (c: cl). ~(memP (eff, op, c) l))
