(**
 * F*'s standard `ulib/ml/app/Prims.ml` is too heavy for JS bundling due to its dependencies 
 * on `zarith`, `yojson`, and `ppx_deriving`. Because the extracted output only references 
 * type aliases, this file serves as a minimal replacement containing only those aliases.
 *
 * If you ever need to append to this file (for instance, starting to use `Prims.int`), 
 * consider it a red flag that `zarith` is being pulled into the JS bundle. 
 * When that happens, refactor the F* implementation rather than expanding this file.
 *)
type string = String.t
type bool = Bool.t
type 'a list = 'a Stdlib.List.t = [] | (::) of 'a * 'a list
