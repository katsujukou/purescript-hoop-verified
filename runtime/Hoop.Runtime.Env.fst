(**
 * The reference realisation of `Hoop.Runtime.Env`.
 *
 * An environment is the list of levels, innermost first; `extend` is `::`,
 * `lookup` is the obvious walk, and the environment below an evidence is
 * literally the tail the walk stopped at -- which is why no notion of object
 * identity is needed anywhere.
 *
 * It differs from the specification view in one respect. A level here keeps the
 * `Hoop.Runtime.Handlers.keyset` the handler table handed over, not the flat
 * `list key` a `level` carries, and `lookup` asks it `contains` rather than
 * calling `mem` on a list. That is the whole of the difference, and the reason
 * for it is that this walk is the machine's hot loop: one `perform` asks every
 * handler between the perform site and the one that catches it, and asking a
 * flat list costs a comparison per operation those handlers declare while
 * asking a keyset -- which groups the operations under their effect -- costs a
 * comparison per *effect* on a miss.
 *
 * `levels` therefore projects each stored keyset through `keyset_view`, and
 * every proof below is against that projection, so the interface is discharged
 * with the levels it specifies. Nothing else in the development sees a keyset.
 *
 * It exists to show the interface is consistent -- that something satisfies it
 * with no `assume` and no `admit` -- and it is also the realisation that ships.
 *)
module Hoop.Runtime.Env

open FStar.List.Tot
open Hoop.Runtime.Handlers

(**
 * A level as stored: the keyset, and the prompt. The `keys` field of the
 * specification's `level` is this keyset's view.
 *)
noeq
type ilevel (a: Type u#x) : Type u#x = {
  ikeys : keyset;
  ipayload : a;
}

let env a = list (ilevel a)

(* The projection to the specification view. Ghost, since `keyset_view` is. *)
let rec view (#a: Type) (w: list (ilevel a)) : GTot (list (level a)) (decreases w) =
  match w with
  | [] -> []
  | il :: rest -> ({ keys = keyset_view il.ikeys; payload = il.ipayload } <: level a) :: view rest

let levels #a w = view w

(* Projection preserves length -- carried by a pattern so that `depth` and
   `is_empty` need no proof term in their bodies; both are extracted. *)
private
let rec view_length (#a: Type) (w: list (ilevel a))
  : Lemma (ensures length (view w) == length w) (decreases w) [SMTPat (view w)]
  = match w with
    | [] -> ()
    | _ :: rest -> view_length rest

let depth #a w = length w

(* Written out rather than as `Nil? w`: the discriminator extracts to
   `Prims.uu___is_Nil`, and `runtime/ml/shim/Prims.ml` realises only the handful
   of Prims that the runtime genuinely needs. *)
let is_empty #a w = match w with | [] -> true | _ :: _ -> false

let empty #a = []

let extend #a w ks x = { ikeys = ks; ipayload = x } :: w

let outer #a w =
  match w with
  | il :: rest ->
      introduce exists (l': level a). view w == l' :: view rest
      with ({ keys = keyset_view il.ikeys; payload = il.ipayload } <: level a) and ();
      rest

let outer_extend #a w ks x = ()

(* The hot loop. `contains` is the keyset's own membership test, which its
   refinement pins to `mem` on the view -- so this walk is `find_level` on the
   levels this environment offers, which is what `lookup_agrees` demands. *)
let rec lookup #a w k
  = match w with
    | [] -> None
    | il :: rest ->
        if contains il.ikeys k
        then Some ({ prompt = il.ipayload; below = rest })
        else lookup rest k

(* `firstn` and the payload projection commute with the view, which is all
   `prompts_between` needs: the levels it keeps are the same either way, and it
   reads only their payloads. *)
private
let rec view_firstn_payloads (#a: Type) (n: int) (w: list (ilevel a))
  : Lemma
      (ensures
        map (fun (l: level a) -> l.payload) (firstn n (view w))
          == map (fun (il: ilevel a) -> il.ipayload) (firstn n w))
      (decreases w)
  = if n <= 0
    then ()
    else match w with
         | [] -> ()
         | _ :: rest -> view_firstn_payloads (n - 1) rest

let prompts_between #a w below =
  view_firstn_payloads (depth w - depth below) w;
  rev (map (fun (il: ilevel a) -> il.ipayload) (firstn (depth w - depth below) w))

(* ------------------------------------------------------------------ *)
(*  Derived facts                                                      *)
(* ------------------------------------------------------------------ *)

let lookup_empty #a k = ()

let lookup_equiv #a w1 w2 k = ()

let lookup_extend_hit #a w ks x k = ()

let lookup_extend_miss #a w ks x k = ()

(* The one fact that needs an induction: the tail `find_level` stops at is a
   suffix of the list it started from, and a strictly shorter one. Everything
   `outer_of` is used for rests on this. Stated on the *view*, since that is
   where `find_level` lives. *)
private
let rec find_level_suffix (#a: Type) (ls: list (level a)) (k: key)
  : Lemma
      (ensures
        (match find_level ls k with
          | None -> True
          | Some (_, outer) ->
              (exists (inner: list (level a)). ls == inner @ outer) /\ length outer < length ls))
      (decreases ls)
  = match ls with
    | [] -> ()
    | l :: rest ->
        if k `mem` l.keys
        then
          introduce exists (inner: list (level a)). l :: rest == inner @ rest
          with [l] and ()
        else begin
          find_level_suffix rest k;
          match find_level rest k with
          | None -> ()
          | Some (_, outer) ->
              eliminate exists (inner: list (level a)). rest == inner @ outer
              with
                introduce exists (inner2: list (level a)). l :: rest == inner2 @ outer
                with (l :: inner) and ()
        end

let lookup_below_outer #a w k = find_level_suffix (levels w) k

let outer_of_refl #a w =
  introduce exists (inner: list (level a)). levels w == inner @ levels w
  with [] and ()

let outer_of_trans #a w1 w2 w3 =
  eliminate exists (i1: list (level a)). levels w2 == i1 @ levels w1
  with
    eliminate exists (i2: list (level a)). levels w3 == i2 @ levels w2
    with
      introduce exists (i: list (level a)). levels w3 == i @ levels w1
      with (i2 @ i1)
      and append_assoc i2 i1 (levels w1)

let depth_extend #a w ks x = ()
