(**
 * F*'s standard `ulib/ml/app/Prims.ml` is too heavy for JS bundling: it realises
 * `Prims.int` with `zarith` and drags in `yojson` and `ppx_deriving` besides.
 * This file is a minimal replacement carrying only what the extracted code
 * actually references.
 *
 * *The red flag to watch for is a dependency on `zarith` or `Stdint`, not the
 * use of `Prims.int` itself.* Realising F*'s unbounded integers as machine
 * integers is F*'s own answer for resource-constrained backends: its C backend
 * does exactly this, and at the same width -- see `krml_checked_int_t` and the
 * `RETURN_OR` macro in KaRaMeL's `krml/internal/compat.h`.
 *
 * *What is assumed.* Every integer surviving extraction here counts stack
 * frames: an installed height, the machine's current height, a list length, a
 * `splitAt` index. `Hoop.Runtime.Env.firstn` and `prompts_between` are
 * `noextract` precisely so that no genuinely signed integer reaches this file,
 * which is what makes the negativity check below a sound overflow test rather
 * than a guess. The assumption reduces to one sentence:
 *
 *     the machine's stack never reaches 2^31 - 1 frames.
 *
 * The bound is 2^31, not 2^62: the JavaScript backend compiles OCaml's `int` to
 * 32 bits whatever the native compiler's width. Melange does it by masking --
 * `n + 1` is emitted as `n + 1 | 0` -- so the wrap to a negative value that the
 * check below tests for happens exactly as it did under js_of_ocaml, and the
 * argument here is unchanged by the change of backend. Reaching it needs on the order of
 * 150 GB of heap for the stack alone, against a default Node heap of 4 GB. And
 * it is checked rather than merely assumed -- the arithmetic below traps on a
 * negative result, so an overflow is a loud failure rather than a silently
 * misplaced continuation split.
 *
 * Extracted code writes `n - h` unqualified under `open Prims`, so it picks up
 * the operators defined here; removing them would fall back to `Stdlib`'s
 * unchecked ones.
 *)

type string = String.t
type bool = Bool.t
type 'a list = 'a Stdlib.List.t = [] | (::) of 'a * 'a list

type int = Stdlib.Int.t
type nat = int
type pos = int

let int_zero : int = 0
let int_one : int = 1

let overflow () : 'a =
  Stdlib.failwith
    "hoop: Prims.nat overflow (the machine stack exceeded the machine integer range)"

let ( + ) (a : int) (b : int) : int =
  let r = Stdlib.( + ) a b in
  if r < 0 then overflow () else r

let ( - ) (a : int) (b : int) : int =
  let r = Stdlib.( - ) a b in
  if r < 0 then overflow () else r

let ( < ) : int -> int -> bool = Stdlib.( < )
let ( <= ) : int -> int -> bool = Stdlib.( <= )
let ( > ) : int -> int -> bool = Stdlib.( > )
let ( >= ) : int -> int -> bool = Stdlib.( >= )

(* The named forms, in case extraction ever emits a partial application. *)
let op_Addition x y = x + y
let op_Subtraction x y = x - y
let op_LessThan x y = x < y
let op_LessThanOrEqual x y = x <= y
let op_GreaterThan x y = x > y
let op_GreaterThanOrEqual x y = x >= y
