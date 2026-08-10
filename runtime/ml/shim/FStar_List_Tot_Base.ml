(**
 * The list operations the extracted runtime actually calls. F*'s own
 * realisation of this module is not used, for the reason given in `Prims.ml`.
 *
 * Only `rev` and `length` are reached from the extracted code; `rev_append` is
 * here because `rev` is written in terms of it. Both are tail-recursive, and
 * that is not a stylistic preference: they run on the machine's hot path over
 * lists whose length is bounded only by the user's stack depth, and jsoo
 * compiles OCaml's native stack onto JavaScript's, where the frame limit is a
 * few tens of thousands. A direct recursion here would be a ceiling on how
 * deeply a user's program may nest, reported as an opaque `RangeError` rather
 * than as anything the program did.
 *
 * *This file is TCB, so it is kept to what is live.* `op_At`, `splitAt` and
 * `mem` were all here and are all gone: the first two had already stopped being
 * called before anyone noticed, and `mem` went when `Hoop.Runtime.Handlers`
 * grew `mem_string`. That last one is worth remembering -- `mem` was the only
 * polymorphic comparison left in the shipped runtime, and every one of its calls
 * was reaching js_of_ocaml's `caml_compare_val`, whose `caml_compare_val_tag`
 * runs a regular expression per operand to discover that its arguments are
 * strings. Removing it took 13% off a State-heavy loop and 37% off the bundle,
 * because jsoo could then eliminate the whole `caml_compare_val` machinery.
 * Guard (c) in `scripts/build-runtime.sh` is what keeps it out.
 *
 * So: if a definition here stops being referenced, delete it rather than
 * leaving it. Anything in this file is trusted, and dead trusted code is the
 * kind that is still trusted when someone makes it live again.
 *)

let rev_append (l1 : 'a list) (l2 : 'a list) : 'a list =
  let rec go acc = function
    | [] -> acc
    | hd :: tl -> go (hd :: acc) tl
  in
  go l2 l1

let rev (xs : 'a list) : 'a list = rev_append xs []

(* Returns `Prims.nat`, i.e. a native int -- see `Prims.ml` for why that is
   sound and what it assumes. The final check is the same overflow trap as the
   one on `Prims.( + )`, hoisted out of the loop: a list long enough to wrap the
   counter cannot be built in the first place, but saying so loudly beats
   returning a negative length into code that has been verified against `nat`. *)
let length (xs : 'a list) : int =
  let rec go n = function [] -> n | _ :: tl -> go (n + 1) tl in
  let n = go 0 xs in
  if n < 0 then
    Stdlib.failwith "hoop: list length overflowed the machine integer range"
  else n
