(**
 * The reference realisation of `Hoop.Runtime.Handlers`.
 *
 * A table is its own specification view -- the flat entry list -- together with
 * two things derived from it once, when the table is built: the same clauses
 * *grouped by effect*, and the keyset of that grouping. `lookup_clause` and
 * `keys` are then a scan of the grouping and a field read respectively, and the
 * refinement on the record makes both correct by construction.
 *
 * *Why the flat list stays.* `mk_handlers` is refined by `table hs == l` and
 * `lookup_clause` by `o == assoc_clause (table hs) eff op`, which is *first
 * match on the original order*. Grouping reorders, so `l` cannot be recovered
 * from the grouping and the two are kept side by side: the list is the
 * specification anchor and is never read at run time, the grouping is what runs.
 * Duplicate keys cannot arise from the FFI -- JS object keys are unique per
 * level -- but `mk_handlers` takes an arbitrary list, so `group` below is built
 * to preserve first-match shadowing on one anyway.
 *
 * *Why the grouping is worth having.* A miss -- the common case, since every
 * handler between a `perform` and the one that catches it is asked first --
 * costs one comparison per *effect* rather than one per *operation*. That is the
 * whole reason `keyset` is abstract; see the header of the interface.
 *
 * *Why the list operations below are written out.* The extracted runtime links
 * against `runtime/ml/shim/FStar_List_Tot_Base.ml`, which realises only the
 * handful of operations the machine genuinely needs; `assoc` and `map` are not
 * among them, and adding them would grow the hand-written part of the trusted
 * base for two three-line functions. `op_lookup` and `op_names` recurse over one
 * effect's operations, whose length is fixed by the handler rather than by the
 * user's program, so the depth bound the shim exists to respect is not at stake.
 *)
module Hoop.Runtime.Handlers

open FStar.List.Tot

(* ------------------------------------------------------------------ *)
(*  One effect's operations                                            *)
(* ------------------------------------------------------------------ *)

(** First-match lookup among the operations of one effect. *)
let rec op_lookup (#cl: Type) (ops: list (string & cl)) (op: string)
  : Tot (option cl) (decreases ops)
  = match ops with
    | [] -> None
    | (o, c) :: rest -> if o = op then Some c else op_lookup rest op

(** The names of those operations, which is what the keyset keeps. *)
let rec op_names (#cl: Type) (ops: list (string & cl)) : Tot (list string) (decreases ops) =
  match ops with
  | [] -> []
  | (o, _) :: rest -> o :: op_names rest

private
let rec mem_op_names (#cl: Type) (ops: list (string & cl)) (op: string)
  : Lemma
      (ensures (op `mem` op_names ops) <==> Some? (op_lookup ops op))
      (decreases ops)
  = match ops with
    | [] -> ()
    | _ :: rest -> mem_op_names rest op

(* ------------------------------------------------------------------ *)
(*  Key sets: effects, each with the operations it declares            *)
(* ------------------------------------------------------------------ *)

(**
 * A keyset is an association list from an effect label to the operations
 * declared under it -- the shape a nested `{eff: {op: _}}` object has, with the
 * clauses dropped.
 *)
let keyset = list (string & list string)

(* The keys one group denotes. Ghost only: nothing computes it. *)
let effect_keys (e: string) (ops: list string) : GTot (list key) =
  map (fun (o: string) -> ((e, o) <: key)) ops

let rec keyset_view s =
  match s with
  | [] -> []
  | (e, ops) :: rest -> effect_keys e ops @ keyset_view rest

(* Membership in one group, spelt out for the solver: `mem` compares the pairs,
   the scan compares the components. *)
private
let rec mem_effect_keys (e: string) (ops: list string) (eff op: string)
  : Lemma
      (ensures ((eff, op) `mem` effect_keys e ops) <==> (e = eff /\ op `mem` ops))
      (decreases ops)
  = match ops with
    | [] -> ()
    | _ :: rest -> mem_effect_keys e rest eff op

(**
 * Membership, computed -- the machine's hot loop, run once per level crossed by
 * every `perform`.
 *
 * The scan continues past a group whose effect matched but whose operations did
 * not. That costs nothing in practice -- a keyset built by `mk_handlers` names
 * each effect once, so the continuation is over the groups that would have been
 * scanned anyway -- and it buys correctness against *every* keyset rather than
 * only against well-formed ones, which is one invariant fewer to carry through
 * `handlers`, through `Hoop.Runtime.Env.extend`, and into the level records.
 *)
private
let rec contains_aux (s: keyset) (eff op: string) : Tot bool (decreases s) =
  match s with
  | [] -> false
  | (e, ops) :: rest -> (e = eff && op `mem` ops) || contains_aux rest eff op

(* Carried by a pattern rather than called from the body of `contains`: that
   body is on the machine's hot path and is run by the normaliser in
   `Hoop.Runtime.Test`, so it is kept free of proof terms. *)
private
let rec contains_aux_correct (s: keyset) (eff op: string)
  : Lemma
      (ensures contains_aux s eff op <==> ((eff, op) `mem` keyset_view s))
      (decreases s)
      [SMTPat (contains_aux s eff op)]
  = match s with
    | [] -> ()
    | (e, ops) :: rest ->
        mem_effect_keys e ops eff op;
        append_mem (effect_keys e ops) (keyset_view rest) (eff, op);
        contains_aux_correct rest eff op

(* The pair is taken apart by a pattern match rather than with `fst` and `snd`,
   which would call into `FStar_Pervasives_Native` -- see the module header. *)
let contains s k = match k with | (eff, op) -> contains_aux s eff op

(* ------------------------------------------------------------------ *)
(*  The grouped clause table                                           *)
(* ------------------------------------------------------------------ *)

(** One effect, with its operations and their clauses -- in the order the entry
    list gave them, which is what keeps shadowing right. *)
let gentry (cl: Type u#a) : Type u#a = string & list (string & cl)

(** The nested object, in list form. *)
let gtable (cl: Type u#a) : Type u#a = list (gentry cl)

(**
 * Lookup in the grouping: find the effect, then the operation under it.
 *
 * As in `contains_aux`, a group whose effect matched but which has no clause for
 * the operation does not end the scan. Same reason: the equation below then
 * holds of *any* grouping, so nothing has to establish that a table names each
 * effect once.
 *)
let rec glookup (#cl: Type) (g: gtable cl) (eff op: string)
  : Tot (option cl) (decreases g)
  = match g with
    | [] -> None
    | (e, ops) :: rest ->
        if e = eff
        then (match op_lookup ops op with
              | Some c -> Some c
              | None -> glookup rest eff op)
        else glookup rest eff op

(**
 * Adding one entry to a grouping, *in front of* whatever is already there for
 * its key: the operation goes to the head of its effect's list, and a new effect
 * to the head of the grouping.
 *
 * `group` folds from the *end* of the entry list, so entries are inserted
 * latest-first and each earlier one lands ahead of the entries it shadows. That
 * is what makes `glookup_group` -- first match in the grouping is first match in
 * the list -- true rather than merely true of duplicate-free lists. It also
 * leaves the operations of an effect in their original relative order, and the
 * effects themselves in order of first occurrence.
 *)
let rec ginsert (#cl: Type) (g: gtable cl) (e o: string) (c: cl)
  : Tot (gtable cl) (decreases g)
  = match g with
    | [] -> [(e, [(o, c)])]
    | (e', ops) :: rest ->
        if e' = e
        then (e', (o, c) :: ops) :: rest
        else (e', ops) :: ginsert rest e o c

let rec group (#cl: Type) (l: list (entry cl)) : Tot (gtable cl) (decreases l) =
  match l with
  | [] -> []
  | (e, o, c) :: rest -> ginsert (group rest) e o c

(* Inserting an entry shadows exactly its own key and nothing else. The one
   induction the grouping needs; note it holds of any `g`, well formed or not. *)
private
let rec glookup_ginsert (#cl: Type) (g: gtable cl) (e o: string) (c: cl) (eff op: string)
  : Lemma
      (ensures
        glookup (ginsert g e o c) eff op
          == (if e = eff && o = op then Some c else glookup g eff op))
      (decreases g)
  = match g with
    | [] -> ()
    | (e', _) :: rest -> if e' = e then () else glookup_ginsert rest e o c eff op

(** **The grouping answers what the flat list answers**, shadowing included. *)
private
let rec glookup_group (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Lemma
      (ensures glookup (group l) eff op == assoc_clause l eff op)
      (decreases l)
      [SMTPat (glookup (group l) eff op)]
  = match l with
    | [] -> ()
    | (e, o, c) :: rest ->
        glookup_group rest eff op;
        glookup_ginsert (group rest) e o c eff op

(** The keyset of a grouping: the same shape with the clauses dropped, so the
    environment's copy costs one cell per effect and per operation and never
    retains a clause. *)
let rec gkeys (#cl: Type) (g: gtable cl) : Tot keyset (decreases g) =
  match g with
  | [] -> []
  | (e, ops) :: rest -> (e, op_names ops) :: gkeys rest

(* The induction: the scan of the keyset and the scan of the grouping descend
   together, group by group. *)
private
let rec contains_aux_gkeys (#cl: Type) (g: gtable cl) (eff op: string)
  : Lemma
      (ensures contains_aux (gkeys g) eff op <==> Some? (glookup g eff op))
      (decreases g)
  = match g with
    | [] -> ()
    | (_, ops) :: rest ->
        mem_op_names ops op;
        contains_aux_gkeys rest eff op

(** **The cached keyset is exactly what the grouping has clauses for.** Both
    forms, since the machine asks with `contains` and the specifications with
    `mem` on the view; the second is the first read through the refinement on
    `contains`. *)
private
let contains_gkeys (#cl: Type) (g: gtable cl) (eff op: string)
  : Lemma
      (ensures
        (contains (gkeys g) (eff, op) <==> Some? (glookup g eff op)) /\
        (((eff, op) `mem` keyset_view (gkeys g)) <==> Some? (glookup g eff op)))
      [SMTPatOr [[SMTPat (contains (gkeys g) (eff, op))];
                 [SMTPat ((eff, op) `mem` keyset_view (gkeys g))]]]
  = contains_aux_gkeys g eff op

(* ------------------------------------------------------------------ *)
(*  The table                                                          *)
(* ------------------------------------------------------------------ *)

(* The invariant relating the two derived fields to the entries. Stated with
   `assoc_clause` rather than `lookup_clause`, which is defined against a table
   and would be circular here. *)
let table_ok (#cl: Type) (l: list (entry cl)) (g: gtable cl) (ks: keyset) : prop =
  (forall (eff op: string). glookup g eff op == assoc_clause l eff op) /\
  (forall (eff op: string). contains ks (eff, op) <==> Some? (assoc_clause l eff op)) /\
  (forall (eff op: string).
    ((eff, op) `mem` keyset_view ks) <==> Some? (assoc_clause l eff op))

(* The only induction the interface needs beyond the above: what
   `keys_mk_handlers` reports. *)
let rec entry_keys_correct (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Lemma
      (ensures ((eff, op) `mem` entry_keys l) <==> Some? (assoc_clause l eff op))
      (decreases l)
  = match l with
    | [] -> ()
    | (e, o, _) :: rest ->
        (* `mem` compares the pairs, `assoc_clause` compares the components;
           the two agree, but the solver is told so rather than left to find it. *)
        assert (((eff, op) = (e, o)) <==> (e = eff && o = op));
        entry_keys_correct rest eff op

(**
 * The representation: the entries, the same clauses grouped by effect, and the
 * keyset of that grouping.
 *
 * A record rather than a tuple, so that the extracted OCaml projects a field of
 * a type declared here instead of calling `FStar_Pervasives_Native.fst` -- the
 * runtime links against a hand-written shim for that module
 * (`runtime/ml/shim/`), and there is no reason to grow it for this.
 *
 * `entries` is never read at run time; it is the ghost view `table` and the
 * anchor every specification is written against. The extracted code keeps the
 * field -- `table` being ghost does not make the field erasable -- at a cost of
 * one pointer per table.
 *)
noeq
type htable (cl: Type u#a) : Type u#a = {
  entries : list (entry cl);
  grouped : gtable cl;
  key_cache : keyset;
}

(* The `u#a` must agree with the `val` in the interface; this is where a
   disagreement surfaces, and not in terms that name a universe. See the
   interface's module header. *)
let handlers (cl: Type u#a) : Type u#a =
  h: htable cl { table_ok h.entries h.grouped h.key_cache }

let table #cl hs = hs.entries

let lookup_clause #cl hs eff op = glookup hs.grouped eff op

let keys #cl hs = hs.key_cache

(* Both derived structures are built here, once per table -- which is once per
   `Handle` -- and the two patterns above discharge the invariant with no proof
   term left in the body. *)
let mk_handlers #cl l =
  let g = group l in
  { entries = l; grouped = g; key_cache = gkeys g }

(* ------------------------------------------------------------------ *)
(*  Derived facts                                                      *)
(* ------------------------------------------------------------------ *)

let lookup_clause_spec #cl hs eff op = ()

let keys_correct #cl hs eff op = ()

let table_mk_handlers #cl l = ()

let lookup_clause_mk_handlers #cl l eff op = ()

let keys_mk_handlers #cl l eff op = entry_keys_correct l eff op

let rec assoc_clause_memP #cl l eff op
  = match l with
    | [] -> ()
    | (e, o, _) :: rest -> if e = eff && o = op then () else assoc_clause_memP rest eff op

let rec assoc_clause_none #cl l eff op
  = match l with
    | [] -> ()
    | (e, o, _) :: rest -> assoc_clause_none rest eff op
