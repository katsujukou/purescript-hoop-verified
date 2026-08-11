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
 * A keyset is one *level's worth* of names, and a level is either a prompt or a
 * cell -- hence the two constructors, which are the two constructors of `key`
 * seen from the other side.
 *
 * `KOps` is an association list from an effect label to the operations declared
 * under it: the shape a nested `{eff: {op: _}}` object has, with the clauses
 * dropped. `KVar` is a single cell label.
 *
 * A record with both a group list and a label list would be more uniform and is
 * what a set-like reading would suggest, but nothing ever needs a keyset holding
 * both: `keys` is always a table's operations and `var_keyset` is always one
 * cell. The sum says so, and costs the hot loop one fewer field to read.
 *)
type ikeyset =
  | KOps : groups:list (string & list string) -> ikeyset
  | KVar : label:string -> ikeyset

let keyset = ikeyset

(* The keys one group denotes. Ghost only: nothing computes it. *)
let effect_keys (e: string) (ops: list string) : GTot (list key) =
  map (fun (o: string) -> OpKey e o) ops

(* The view of a grouping. Split out from `keyset_view` so that the induction
   below runs on the list rather than under a constructor. *)
let rec groups_view (g: list (string & list string)) : GTot (list key) =
  match g with
  | [] -> []
  | (e, ops) :: rest -> effect_keys e ops @ groups_view rest

let keyset_view s =
  match s with
  | KOps g -> groups_view g
  | KVar l -> [VarKey l]

(* Membership in one group, spelt out for the solver: `mem` compares the keys,
   the scan compares the components. *)
private
let rec mem_effect_keys (e: string) (ops: list string) (eff op: string)
  : Lemma
      (ensures (OpKey eff op `mem` effect_keys e ops) <==> (e = eff /\ op `mem` ops))
      (decreases ops)
  = match ops with
    | [] -> ()
    | _ :: rest -> mem_effect_keys e rest eff op

(* A group denotes operations only -- the half of the sorts' disjointness that
   needs an induction. Carried by a pattern: it is wanted at every `PromptF`
   crossed by a cell lookup, and never wanted with `g` any particular list. *)
private
let rec mem_effect_keys_var (e: string) (ops: list string) (l: string)
  : Lemma (ensures ~(VarKey l `mem` effect_keys e ops)) (decreases ops)
  = match ops with
    | [] -> ()
    | _ :: rest -> mem_effect_keys_var e rest l

private
let rec groups_view_no_var (g: list (string & list string)) (l: string)
  : Lemma
      (ensures ~(VarKey l `mem` groups_view g))
      (decreases g)
      [SMTPat (VarKey l `mem` groups_view g)]
  = match g with
    | [] -> ()
    | (e, ops) :: rest ->
        mem_effect_keys_var e ops l;
        append_mem (effect_keys e ops) (groups_view rest) (VarKey l);
        groups_view_no_var rest l

(**
 * **`mem` at `string`**, written out.
 *
 * `FStar.List.Tot.Base.mem` would do, and the shim already realises it, so
 * unlike `op_lookup` and `op_names` above this one is not written out to keep
 * the trusted base small. It is written out for what it extracts to.
 *
 * The shim's `mem` is polymorphic, so its `hd = x` extracts to OCaml's
 * *structural* equality: `caml_equal`, which reaches `caml_compare_val` and
 * tests each operand with `caml_is_ml_string` -- a regular-expression match per
 * operand, per element scanned. At a known `string` the OCaml compiler picks
 * `caml_string_equal` instead, which js_of_ocaml compiles to `===`. Every other
 * comparison in this module is already monomorphic and already gets that -- the
 * OCaml compiler specialises `=` on its own wherever the type is a known
 * `string`, so nothing else here needed changing. This call was the one place
 * the machine's hot loop still paid for a generic comparison, and dropping it
 * is worth around a tenth of the running time of a State-heavy loop.
 *
 * The refinement is what lets the proofs below go on speaking of `mem`: the
 * result is the *same boolean*, so `contains_aux_correct` and everything it
 * feeds are unchanged.
 *)
private
let rec mem_string (x: string) (l: list string)
  : Tot (b: bool { b <==> x `mem` l }) (decreases l)
  = match l with
    | [] -> false
    | hd :: tl -> hd = x || mem_string x tl

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
let rec contains_aux (g: list (string & list string)) (eff op: string)
  : Tot bool (decreases g)
  = match g with
    | [] -> false
    | (e, ops) :: rest -> (e = eff && op `mem_string` ops) || contains_aux rest eff op

(* Carried by a pattern rather than called from the body of `contains`: that
   body is on the machine's hot path and is run by the normaliser in
   `Hoop.Runtime.Test`, so it is kept free of proof terms. *)
private
let rec contains_aux_correct (g: list (string & list string)) (eff op: string)
  : Lemma
      (ensures contains_aux g eff op <==> (OpKey eff op `mem` groups_view g))
      (decreases g)
      [SMTPat (contains_aux g eff op)]
  = match g with
    | [] -> ()
    | (e, ops) :: rest ->
        mem_effect_keys e ops eff op;
        append_mem (effect_keys e ops) (groups_view rest) (OpKey eff op);
        contains_aux_correct rest eff op

(* The two sorts are matched together, so a level of the wrong sort answers
   `false` in one comparison -- which is the whole of what makes a prompt
   transparent to a cell lookup and a cell transparent to a dispatch. *)
let contains s k =
  match s, k with
  | KOps g, OpKey eff op -> contains_aux g eff op
  | KVar l, VarKey l' -> l = l'
  | KOps _, VarKey _ -> false
  | KVar _, OpKey _ _ -> false

let var_keyset l = KVar l

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

(* ------------------------------------------------------------------ *)
(*  The same two scans, projecting the clause out                      *)
(*                                                                     *)
(*  The grouping stores `found_clause cl`, because the kinds are        *)
(*  computed once when the table is built and never at lookup time.     *)
(*  `lookup_clause` therefore has a field to read -- but that is ALL it  *)
(*  has to do: these two return the stored clause directly rather than   *)
(*  mapping over the option `glookup` returns, so the hot path allocates *)
(*  exactly what it allocated before this record existed. They are the   *)
(*  realisation of the interface's insistence that `lookup_clause` is a   *)
(*  primitive; see the note there.                                      *)
(* ------------------------------------------------------------------ *)

let rec op_lookup_body (#cl: Type) (ops: list (string & found_clause cl)) (op: string)
  : Tot (option cl) (decreases ops)
  = match ops with
    | [] -> None
    | (o, f) :: rest -> if o = op then Some f.body else op_lookup_body rest op

let rec glookup_body (#cl: Type) (g: gtable (found_clause cl)) (eff op: string)
  : Tot (option cl) (decreases g)
  = match g with
    | [] -> None
    | (e, ops) :: rest ->
        if e = eff
        then (match op_lookup_body ops op with
              | Some c -> Some c
              | None -> glookup_body rest eff op)
        else glookup_body rest eff op

(* The projecting scan finds what the scan finds, clause for clause. Carried by
   patterns: both facts are wanted at arbitrary groupings, and the whole point of
   the duplication is that nothing downstream should have to know about it. *)
private
let rec op_lookup_body_spec (#cl: Type) (ops: list (string & found_clause cl)) (op: string)
  : Lemma
      (ensures op_lookup_body ops op == map_opt (fun (f: found_clause cl) -> f.body)
                                                (op_lookup ops op))
      (decreases ops)
      [SMTPat (op_lookup_body ops op)]
  = match ops with
    | [] -> ()
    | _ :: rest -> op_lookup_body_spec rest op

private
let rec glookup_body_spec (#cl: Type) (g: gtable (found_clause cl)) (eff op: string)
  : Lemma
      (ensures glookup_body g eff op == map_opt (fun (f: found_clause cl) -> f.body)
                                                (glookup g eff op))
      (decreases g)
      [SMTPat (glookup_body g eff op)]
  = match g with
    | [] -> ()
    | (e, ops) :: rest ->
        op_lookup_body_spec ops op;
        glookup_body_spec rest eff op

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

(**
 * **Classifying the entry list**, once, on the way into the grouping.
 *
 * This is where `classify` is spent -- the only place it is ever applied. A
 * lookup reads a kind that was decided when the table was built, so the cost of
 * knowing a clause's kind is one field, paid once per `Handle`, and never a
 * function call on the dispatch path.
 *)
let rec map_found (#cl: Type) (classify: cl -> clause_kind) (l: list (entry cl))
  : Tot (list (entry (found_clause cl))) (decreases l)
  = match l with
    | [] -> []
    | (e, o, c) :: rest -> (e, o, found_of classify c) :: map_found classify rest

(* Classifying commutes with association lookup -- of course it does; it is
   pointwise. Carried by a pattern because `mk_handlers` needs it at every
   `(eff, op)` at once. *)
private
let rec assoc_map_found (#cl: Type) (classify: cl -> clause_kind) (l: list (entry cl))
    (eff op: string)
  : Lemma
      (ensures assoc_clause (map_found classify l) eff op
                 == map_opt (found_of classify) (assoc_clause l eff op))
      (decreases l)
      [SMTPat (assoc_clause (map_found classify l) eff op)]
  = match l with
    | [] -> ()
    | _ :: rest -> assoc_map_found classify rest eff op

(** The keyset of a grouping: the same shape with the clauses dropped, so the
    environment's copy costs one cell per effect and per operation and never
    retains a clause. *)
let rec gkeys_groups (#cl: Type) (g: gtable cl)
  : Tot (list (string & list string)) (decreases g)
  = match g with
    | [] -> []
    | (e, ops) :: rest -> (e, op_names ops) :: gkeys_groups rest

let gkeys (#cl: Type) (g: gtable cl) : Tot keyset = KOps (gkeys_groups g)

(* The induction: the scan of the keyset and the scan of the grouping descend
   together, group by group. *)
private
let rec contains_aux_gkeys (#cl: Type) (g: gtable cl) (eff op: string)
  : Lemma
      (ensures contains_aux (gkeys_groups g) eff op <==> Some? (glookup g eff op))
      (decreases g)
  = match g with
    | [] -> ()
    | (_, ops) :: rest ->
        mem_op_names ops op;
        contains_aux_gkeys rest eff op

(** **The cached keyset is exactly what the grouping has clauses for, and holds
    no cell.** Every form, since the machine asks with `contains` and the
    specifications with `mem` on the view; the view forms are the computed ones
    read through the refinement on `contains`, and the `VarKey` ones are
    `groups_view_no_var` under the `KOps` constructor. *)
private
let contains_gkeys (#cl: Type) (g: gtable cl) (eff op: string)
  : Lemma
      (ensures
        (contains (gkeys g) (OpKey eff op) <==> Some? (glookup g eff op)) /\
        ((OpKey eff op `mem` keyset_view (gkeys g)) <==> Some? (glookup g eff op)))
      [SMTPatOr [[SMTPat (contains (gkeys g) (OpKey eff op))];
                 [SMTPat (OpKey eff op `mem` keyset_view (gkeys g))]]]
  = contains_aux_gkeys g eff op

private
let gkeys_no_var (#cl: Type) (g: gtable cl) (l: string)
  : Lemma
      (ensures ~(contains (gkeys g) (VarKey l)) /\ ~(VarKey l `mem` keyset_view (gkeys g)))
      [SMTPatOr [[SMTPat (contains (gkeys g) (VarKey l))];
                 [SMTPat (VarKey l `mem` keyset_view (gkeys g))]]]
  = ()

(* ------------------------------------------------------------------ *)
(*  What blocks a borrow                                               *)
(*                                                                     *)
(*  Walked per effect group, which is the shape the answer is a set of. *)
(*  The kind of an operation is read through `glookup` ON THE WHOLE     *)
(*  GROUPING rather than off the group being walked: that is what makes *)
(*  the equivalence below hold of an arbitrary grouping, one naming an  *)
(*  effect twice included, and it costs nothing on a grouping built by  *)
(*  `group`, which names each effect once.                             *)
(* ------------------------------------------------------------------ *)

(* Matched rather than compared. `<>` at `clause_kind` would extract to OCaml's
   polymorphic disequality -- `caml_notequal`, a structural walk -- which guard
   (c) of scripts/build-runtime.sh forbids in the bundle, and rightly: the
   machine compares nothing but labels. This is a tag test. *)
let is_fast (k: clause_kind) : Tot bool =
  match k with
  | KFast -> true
  | _ -> false

(* Does any operation of this group dispatch to a clause that is not `KFast`?
   Written with nested `if`s and no `not`: the extracted runtime links against
   `runtime/ml/shim/Prims.ml`, which realises only what the machine needs, and
   `op_Negation` is not among it. Adding it would grow the hand-written trusted
   base for a negation. *)
let rec ops_blocking (#cl: Type)
    (g: gtable (found_clause cl)) (e: string) (ops: list (string & found_clause cl))
  : Tot bool (decreases ops)
  = match ops with
    | [] -> false
    | (o, _) :: rest ->
        (match glookup g e o with
          | Some f -> if is_fast f.kind then ops_blocking g e rest else true
          | None -> ops_blocking g e rest)

let rec blocking_groups (#cl: Type) (g0 g: gtable (found_clause cl))
  : Tot (list string) (decreases g)
  = match g with
    | [] -> []
    | (e, ops) :: rest ->
        let r = blocking_groups g0 rest in
        if ops_blocking g0 e ops
        then (if mem_string e r then r else e :: r)
        else r

(* The property the interface states of the answer, named so that the two halves
   below and `blocking_effects` all speak of one predicate. *)
let blocks (#cl: Type) (g: gtable (found_clause cl)) (e: string) : prop =
  exists (o: string) (f: found_clause cl). glookup g e o == Some f /\ f.kind =!= KFast

private
let rec ops_blocking_sound (#cl: Type)
    (g: gtable (found_clause cl)) (e: string) (ops: list (string & found_clause cl))
  : Lemma (requires ops_blocking g e ops) (ensures blocks g e) (decreases ops)
  = match ops with
    | [] -> ()
    | (o, _) :: rest ->
        (match glookup g e o with
          | Some f ->
              if is_fast f.kind then ops_blocking_sound g e rest
              else introduce exists (o': string) (f': found_clause cl).
                     glookup g e o' == Some f' /\ f'.kind =!= KFast
                   with o f and ()
          | None -> ops_blocking_sound g e rest)

private
let rec ops_blocking_complete (#cl: Type)
    (g: gtable (found_clause cl)) (e: string) (ops: list (string & found_clause cl))
    (o: string) (f: found_clause cl)
  : Lemma
      (requires (o `mem` op_names ops) /\ glookup g e o == Some f /\ f.kind =!= KFast)
      (ensures ops_blocking g e ops)
      (decreases ops)
  = match ops with
    | [] -> ()
    | (o', _) :: rest -> if o' = o then () else ops_blocking_complete g e rest o f

(* A hit really came from a group of this grouping, and the operation is one that
   group declares. This is what lets the walk over groups be complete: the
   witness of `blocks` is found by `glookup` somewhere, and "somewhere" is a
   group the walk visits. *)
private
let rec glookup_mem (#cl: Type)
    (g: gtable (found_clause cl)) (e o: string) (f: found_clause cl)
  : Lemma
      (requires glookup g e o == Some f)
      (ensures exists (ops: list (string & found_clause cl)).
                 (e, ops) `memP` g /\ (o `mem` op_names ops))
      (decreases g)
  = match g with
    | [] -> ()
    | (e', ops) :: rest ->
        if e' = e && Some? (op_lookup ops o)
        then (mem_op_names ops o;
              introduce exists (ops': list (string & found_clause cl)).
                (e, ops') `memP` g /\ (o `mem` op_names ops')
              with ops and ())
        else glookup_mem rest e o f

private
let rec blocking_groups_sound (#cl: Type) (g0 g: gtable (found_clause cl)) (e: string)
  : Lemma
      (requires e `mem` blocking_groups g0 g)
      (ensures blocks g0 e)
      (decreases g)
  = match g with
    | [] -> ()
    | (e', ops) :: rest ->
        if e' = e && ops_blocking g0 e' ops
        then ops_blocking_sound g0 e' ops
        else blocking_groups_sound g0 rest e

private
let rec blocking_groups_complete (#cl: Type) (g0 g: gtable (found_clause cl))
    (e: string) (ops: list (string & found_clause cl)) (o: string) (f: found_clause cl)
  : Lemma
      (requires (e, ops) `memP` g /\ (o `mem` op_names ops) /\
                glookup g0 e o == Some f /\ f.kind =!= KFast)
      (ensures e `mem` blocking_groups g0 g)
      (decreases g)
  = match g with
    | [] -> ()
    | (e', ops') :: rest ->
        eliminate ((e', ops') == (e, ops)) \/ ((e, ops) `memP` rest)
        with ops_blocking_complete g0 e ops o f
        and  blocking_groups_complete g0 rest e ops o f

(** **The walk reports exactly the blocking effects.** *)
private
let blocking_groups_correct (#cl: Type) (g: gtable (found_clause cl))
  : Lemma (forall (e: string). (e `mem` blocking_groups g g) <==> blocks g e)
  = introduce forall (e: string). (e `mem` blocking_groups g g) <==> blocks g e
    with begin
      introduce (e `mem` blocking_groups g g) ==> blocks g e
      with blocking_groups_sound g g e;
      introduce blocks g e ==> (e `mem` blocking_groups g g)
      with
        eliminate exists (o: string) (f: found_clause cl).
          glookup g e o == Some f /\ f.kind =!= KFast
        with
          (glookup_mem g e o f;
           eliminate exists (ops: list (string & found_clause cl)).
             (e, ops) `memP` g /\ (o `mem` op_names ops)
           with blocking_groups_complete g g e ops o f)
    end

(* ------------------------------------------------------------------ *)
(*  The table                                                          *)
(* ------------------------------------------------------------------ *)

(* The invariant relating the two derived fields to the entries. Stated with
   `assoc_clause` rather than `lookup_clause`, which is defined against a table
   and would be circular here.
   Note which scan the first conjunct names: the CLAUSES the grouping yields are
   the clauses the entry list yields. It says nothing about the kinds, and there
   is nothing for it to say -- an arbitrary well-formed table is entitled to
   whatever kinds it holds, and only `mk_handlers` ties them to a classifier. *)
let table_ok (#cl: Type) (l: list (entry cl)) (g: gtable (found_clause cl)) (ks: keyset) : prop =
  (forall (eff op: string). glookup_body g eff op == assoc_clause l eff op) /\
  (forall (eff op: string). contains ks (OpKey eff op) <==> Some? (assoc_clause l eff op)) /\
  (forall (eff op: string).
    ((OpKey eff op) `mem` keyset_view ks) <==> Some? (assoc_clause l eff op)) /\
  (forall (l2: string). ~(contains ks (VarKey l2))) /\
  (forall (l2: string). ~((VarKey l2) `mem` keyset_view ks))

(* The only induction the interface needs beyond the above: what
   `keys_mk_handlers` reports. *)
let rec entry_keys_correct (#cl: Type) (l: list (entry cl)) (eff op: string)
  : Lemma
      (ensures ((OpKey eff op) `mem` entry_keys l) <==> Some? (assoc_clause l eff op))
      (decreases l)
  = match l with
    | [] -> ()
    | (e, o, _) :: rest ->
        (* `mem` compares the keys, `assoc_clause` compares the components;
           the two agree, but the solver is told so rather than left to find it. *)
        assert ((OpKey eff op = OpKey e o) <==> (e = eff && o = op));
        entry_keys_correct rest eff op

(**
 * The representation: the entries, the same clauses grouped by effect and
 * carrying the kind the classifier gave them, and the keyset of that grouping.
 *
 * *One grouping, not two.* Storing the clauses a second time without their kinds
 * would keep `lookup_clause` character for character as it was, at the cost of
 * building and retaining a second copy of the whole structure on every
 * `Handle` -- and a `Handle` is not rare: a closure-capturing handler such as
 * `catch` builds a fresh table at every call, which is what the handler
 * installation benchmark measures. The kind rides along in the record instead,
 * and `glookup_body` above pays for it with a field read at the hit, not with an
 * allocation and not with a comparison.
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
  grouped : gtable (found_clause cl);
  key_cache : keyset;
}

(* The `u#a` must agree with the `val` in the interface; this is where a
   disagreement surfaces, and not in terms that name a universe. See the
   interface's module header. *)
let handlers (cl: Type u#a) : Type u#a =
  h: htable cl { table_ok h.entries h.grouped h.key_cache }

let table #cl hs = hs.entries

let lookup_clause #cl hs eff op = glookup_body hs.grouped eff op

let lookup_handler #cl hs eff op = glookup hs.grouped eff op

(* Both scans descend the same grouping and stop at the same entry; the
   pattern-carried `glookup_body_spec` is the whole of the argument. *)
let lookup_handler_agrees #cl hs eff op = ()

let keys #cl hs = hs.key_cache

(* Both derived structures are built here, once per table -- which is once per
   `Handle` -- and the patterns above discharge the invariant with no proof term
   left in the body. `map_found` is the classifier's one and only application
   site. *)
let mk_handlers #cl classify l =
  let g = group (map_found classify l) in
  { entries = l; grouped = g; key_cache = gkeys g }

(**
 * **Computed on demand, not cached** -- for now, and the interface cannot tell.
 *
 * The design note has this as a cache filled at `mk_handlers` time, beside the
 * keyset. It is not one yet because nothing calls it yet: the borrowability
 * check belongs to the `Weave` transition, which does not exist, and until it
 * does a cache would tax every `Handle` -- the operation the handler
 * installation benchmark measures -- to precompute an answer no one asks for.
 * The refinement is what callers see, and it is the same either way, so the day
 * a weave asks this question often enough to matter the field can be added with
 * nothing downstream to revisit.
 *)
let blocking_effects #cl hs =
  blocking_groups_correct hs.grouped;
  blocking_groups hs.grouped hs.grouped

(* ------------------------------------------------------------------ *)
(*  Derived facts                                                      *)
(* ------------------------------------------------------------------ *)

let lookup_clause_spec #cl hs eff op = ()

let keys_correct #cl hs eff op = ()

let keys_no_var #cl hs l = ()

let table_mk_handlers #cl classify l = ()

let lookup_clause_mk_handlers #cl classify l eff op = ()

let lookup_handler_mk_handlers #cl classify l eff op = ()

let keys_mk_handlers #cl classify l eff op = entry_keys_correct l eff op

let rec assoc_clause_memP #cl l eff op
  = match l with
    | [] -> ()
    | (e, o, _) :: rest -> if e = eff && o = op then () else assoc_clause_memP rest eff op

let rec assoc_clause_none #cl l eff op
  = match l with
    | [] -> ()
    | (e, o, _) :: rest -> assoc_clause_none rest eff op
