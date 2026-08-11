(**
 * The realisation of `Hoop.Runtime.Api`: eight applications of a constructor.
 *
 * There is nothing to prove here and that is the design. The interface's
 * content is entirely in what it does NOT declare -- `Splice`, `Weave`,
 * `BindF`, `ParamF`, `PromptF` -- so each definition below is the identity on
 * the corresponding `Hoop.Runtime.Syntax` node, and each refinement in the
 * interface is discharged by reflexivity.
 *
 * The one thing to keep an eye on is that these stay *definitions* and stay
 * *extracted*. They are plain `let`s rather than `unfold`s on purpose: an
 * `unfold` reduces away at typechecking and would leave the extracted module
 * with no such value for `runtime/ml/melange/hoop_ffi.ml` to call, and the
 * boundary would go back to naming `Hoop_Runtime_Syntax` because it would have
 * nothing else to name.
 *)
module Hoop.Runtime.Api

open Hoop.Runtime.Syntax
open Hoop.Runtime

let var #v #cl value = Var value

let op #v #cl c fn = Op c fn

let perform #v #cl eff op payload = Perform eff op payload

let performS #v #cl eff op payload = PerformS eff op payload

let handle #v #cl hs pure body = Handle hs pure body

let newP #v #cl label init body = NewP label init body

let readP #v #cl label = ReadP label

let writeP #v #cl label value = WriteP label value
