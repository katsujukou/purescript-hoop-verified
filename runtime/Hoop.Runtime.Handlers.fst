(**
 * The reference realisation of `Hoop.Runtime.Handlers`.
 *
 * A table is its own specification view paired with its derived keys, so that
 * `keys` is a projection rather than a traversal; the refinement on the pair
 * makes the cache correct by construction. `lookup_clause` is a linear scan,
 * not the two property accesses a nested-object realisation would perform:
 * this module exists to show the interface is consistent -- that something
 * satisfies it with no `assume` and no `admit` -- and to give the machine a
 * table whose behaviour is manifest to test against.
 *)
module Hoop.Runtime.Handlers

open FStar.List.Tot

(* The invariant relating the cache to the entries. Stated with `assoc_clause`
   rather than `lookup_clause`, which is defined against a table and would be
   circular here. *)
let cache_ok (#cl: Type) (l: list (entry cl)) (ks: list key) : prop =
  forall (eff op: string). ((eff, op) `mem` ks) <==> Some? (assoc_clause l eff op)

(* The only induction this module needs: everything the interface says about
   `keys` is this fact, carried by the refinement on `handlers`. *)
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
 * The representation: the entries, and the keys derived from them.
 *
 * A record rather than a pair, so that the extracted OCaml projects a field of
 * a type declared here instead of calling `FStar_Pervasives_Native.fst` -- the
 * runtime links against a hand-written three-line shim for that module
 * (`runtime/ml/shim/`), and there is no reason to grow it for this.
 *)
noeq
type htable (cl: Type u#a) : Type u#a = {
  entries : list (entry cl);
  key_cache : list key;
}

(* The `u#a` must agree with the `val` in the interface; this is where a
   disagreement surfaces, and not in terms that name a universe. See the
   interface's module header. *)
let handlers (cl: Type u#a) : Type u#a =
  h: htable cl { cache_ok h.entries h.key_cache }

let table #cl hs = hs.entries

let lookup_clause #cl hs eff op = assoc_clause hs.entries eff op

let keys #cl hs = hs.key_cache

let mk_handlers #cl l =
  FStar.Classical.forall_intro_2 (entry_keys_correct l);
  { entries = l; key_cache = entry_keys l }

(* ------------------------------------------------------------------ *)
(*  Derived facts                                                      *)
(* ------------------------------------------------------------------ *)

let lookup_clause_spec #cl hs eff op = ()

let keys_correct #cl hs eff op = ()

let table_mk_handlers #cl l = ()

let lookup_clause_mk_handlers #cl l eff op = ()

let keys_mk_handlers #cl l = ()

let rec assoc_clause_memP #cl l eff op
  = match l with
    | [] -> ()
    | (e, o, _) :: rest -> if e = eff && o = op then () else assoc_clause_memP rest eff op

let rec assoc_clause_none #cl l eff op
  = match l with
    | [] -> ()
    | (e, o, _) :: rest -> assoc_clause_none rest eff op
