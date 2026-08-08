(**
 * The handful of list operations the extracted runtime actually calls. F*'s own
 * realisation of this module is not used, for the reason given in `Prims.ml`.
 *
 * Everything here is tail-recursive, `op_At` included. These run on the
 * machine's hot path with a length bounded only by the user's stack depth, and
 * jsoo compiles OCaml's native stack onto JavaScript's, where the frame limit
 * is a few tens of thousands -- so a direct recursion over a list here would be
 * a ceiling on how deeply a user's program may nest, reported as an opaque
 * `RangeError` rather than as anything the program did. The extra pass `op_At`
 * pays for it costs nothing measurable: it walks the same cells and allocates
 * the same conses as the direct shape.
 *)

let rev_append (l1 : 'a list) (l2 : 'a list) : 'a list =
  let rec go acc = function
    | [] -> acc
    | hd :: tl -> go (hd :: acc) tl
  in
  go l2 l1

let rev (xs : 'a list) : 'a list = rev_append xs []

let op_At (l1 : 'a list) (l2 : 'a list) : 'a list = rev_append (rev l1) l2

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

let mem (x : 'a) (xs : 'a list) : bool =
  let rec go = function [] -> false | hd :: tl -> hd = x || go tl in
  go xs

(* F*'s splitAt truncates rather than failing: `splitAt n l` with `n` past the
   end returns `(l, [])`. *)
let splitAt (n : int) (xs : 'a list) : 'a list * 'a list =
  let rec go acc n l =
    if n <= 0 then (rev acc, l)
    else match l with [] -> (rev acc, []) | hd :: tl -> go (hd :: acc) (n - 1) tl
  in
  go [] n xs
