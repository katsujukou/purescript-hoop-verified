(**
 * The Melange boundary: the same trusted layer as `runtime/ml/hoop_ffi.ml`,
 * against Melange rather than js_of_ocaml.
 *
 * *Why a second one exists.* This file is where F* stops verifying and starts
 * assuming, so it is exactly the layer a backend change is allowed to move --
 * no `.fst` is touched and no proof is restated. What replaces the proof is
 * `test/js/engine-smoke.mjs`, which was written for this responsibility and
 * which the Melange build must pass unchanged.
 *
 * *What Melange buys.* Four of the twelve jsoo externals become identities:
 *
 *   - `string_of_jsstring` / `jsstring_of_string`. A Melange `string` IS a JS
 *     string, so the conversion -- and `jsoo_is_ascii`'s scan of every label on
 *     every `perform` and every `with` -- is gone.
 *   - `array_of_js` / `array_to_js`. A Melange `array` IS a JS array; jsoo's
 *     carry a leading tag, which is why the jsoo build must copy.
 *
 * Those are the two conversions this runtime crosses most: a payload array per
 * `perform`, and `handlers_of_js` converting every key of every table per
 * `with`.
 *
 * *And what it does not.* `wrap_callback` is gone too, but for a different
 * reason: Melange compiles a top-level `let f a b = ...` to a real two-argument
 * JS function, so the entry points below are directly callable from PureScript
 * and the double-wrapping hazard the jsoo file warns about cannot arise. What
 * Melange does NOT remove is the currying trampoline: applying an unknown
 * closure still goes through `Curry._1`, the counterpart of jsoo's `caml_call1`.
 *
 * *Arity is load-bearing.* Every entry point must compile to a JS function of
 * the arity PureScript imports it at (`Fn2`/`Fn3`/`Fn4`). Melange gives that for
 * a syntactic `let f a b c = ...`; it does not for a `let f = fun a -> fun b ->`
 * or for anything that returns a partial application. Keep the definitions in
 * the direct form.
 *)

(* Opaque JS values. Never inspected from the OCaml side. *)
type any

(* --- Representation identities ------------------------------------------- *)

external inject : 'a -> any = "%identity"
external magic : any -> 'a = "%identity"

(* The four that jsoo has to convert and Melange does not. Kept as named
   identities rather than deleted, so the jsoo file and this one stay readable
   against each other. *)
external string_of_jsstring : any -> string = "%identity"
external jsstring_of_string : string -> any = "%identity"
external array_of_js : any -> any array = "%identity"
external array_to_js : any array -> any = "%identity"

(* --- Property access ------------------------------------------------------ *)

external js_get : any -> any -> any = "" [@@mel.get_index]

(* --- The JavaScript primitives, from ./hoop_prim.js ----------------------- *)

external call1 : any -> any -> any = "call1" [@@mel.module "./hoop_prim.js"]
external call2 : any -> any -> any -> any = "call2" [@@mel.module "./hoop_prim.js"]
external is_nullish : any -> bool = "isNullish" [@@mel.module "./hoop_prim.js"]
external is_function : any -> bool = "isFunction" [@@mel.module "./hoop_prim.js"]
external throw_error : string -> 'a = "throwError" [@@mel.module "./hoop_prim.js"]
external fast_fun : any -> any = "fastFun" [@@mel.module "./hoop_prim.js"]
external object_keys : any -> any array = "objectKeys" [@@mel.module "./hoop_prim.js"]
external apply_payload : any -> any -> any = "applyPayload" [@@mel.module "./hoop_prim.js"]
external empty_record : any -> any = "emptyRecord" [@@mel.module "./hoop_prim.js"]
external insert : any -> any -> any -> any = "insert" [@@mel.module "./hoop_prim.js"]

(* The curried builders. Kept in JS because Melange would flatten an OCaml
   definition that returns a function -- see `hoop_prim.js`. *)
external mk_full_clause : any -> any = "mkFullClause" [@@mel.module "./hoop_prim.js"]
external mk_fast_clause : any -> any = "mkFastClause" [@@mel.module "./hoop_prim.js"]
external mk_return : any -> any -> any = "mkReturn" [@@mel.module "./hoop_prim.js"]

(* --- Utilities ------------------------------------------------------------ *)

(* The machine runs the AST at the TAGGED clause type: an entry of a handler
   table is `Full c` or `Fast c`, never a bare handle. *)
type comp = (any, any) Hoop_Runtime.ct

let fail (msg : string) : 'a = throw_error msg

(* --- The two interpreters the machine dispatches through ------------------ *)

(* A fully controllable clause: `(payload[], resume) => comp`. The continuation
   is an OCaml closure of arity one, which under Melange is already a
   one-argument JS function -- no wrapping. *)
let apply_full (clause : any) (payload : any list) (k : any -> comp) : comp =
  let arr = array_to_js (Array.of_list payload) in
  let jk = inject (fun (x : any) -> inject (k x)) in
  magic (call2 clause arr jk)

(* A tail-resumptive clause: `(payload[]) => comp`. There is no continuation to
   pass, and that is the point -- the body runs in place, under the environment
   the handler was installed in, and its value is the operation's result. *)
let apply_fast (clause : any) (payload : any list) : comp =
  magic (call1 clause (array_to_js (Array.of_list payload)))

(* The discriminator between the two clause shapes, and the only place either is
   inspected. `mkFullClauseImpl` produces a JS function; `mkFastClauseImpl`
   produces the object `{ fun }`. Anything else is a malformed clause and is
   reported here, by name, rather than left to fail as an opaque "is not a
   function" from inside the machine. *)
let tag_clause (eff : string) (op : string) (c : any) : any Hoop_Runtime.clause =
  if is_function c then Hoop_Runtime.Full c
  else
    let f = fast_fun c in
    if is_nullish f then
      fail
        ("hoop: the clause for '" ^ eff ^ "." ^ op
         ^ "' is neither a fully controllable (ctl) clause nor a tail-resumptive \
            (fast) one")
    else Hoop_Runtime.Fast f

(* Flatten the nested handler table { [eff]: { [op]: clause } } that PureScript
   hands over into the association list Hoop_Runtime_Handlers works with,
   tagging each entry on the way. Object keys are unique per level, so the
   result never contains a duplicate (eff, op) pair. The conversion happens once
   per Handle, not once per perform.

   This is the loop the jsoo build pays `caml_string_of_jsstring` for, once per
   key: here `string_of_jsstring` is `%identity`. *)
let handlers_of_js (o : any) : (string * string * any Hoop_Runtime.clause) list =
  Array.fold_right
    (fun (eff_key : any) acc ->
       let eff = string_of_jsstring eff_key in
       let ops_obj = js_get o eff_key in
       Array.fold_right
         (fun (op_key : any) acc' ->
            let op = string_of_jsstring op_key in
            (eff, op, tag_clause eff op (js_get ops_obj op_key)) :: acc')
         (object_keys ops_obj) acc)
    (object_keys o) []

(* --- Functions exposed to PureScript -------------------------------------- *)

(* Named exactly as PureScript imports them: Melange exports a module's
   top-level values under their own names, so there is no export table to keep
   in step -- the names here ARE the interface. *)

let pureImpl (value : any) : any = inject (Hoop_Runtime_Syntax.Var value : comp)

let bindImpl (c : any) (fn : any) : any =
  inject (Hoop_Runtime_Syntax.Op (magic c, fun (x : any) -> magic (call1 fn x)) : comp)

let performImpl (eff : any) (op : any) (_evkey : any) (payload : any) : any =
  inject
    (Hoop_Runtime_Syntax.Perform
       ( string_of_jsstring eff,
         string_of_jsstring op,
         Array.to_list (array_of_js payload) )
      : comp)

let withImpl (ret : any) (handlers : any) (body : any) : any =
  let hs = handlers_of_js handlers in
  let r =
    if is_nullish ret then None
    else Some (fun (x : any) -> (magic (call1 ret x) : comp))
  in
  inject
    (Hoop_Runtime_Syntax.Handle (Hoop_Runtime_Handlers.mk_handlers hs, r, magic body)
      : comp)

(* --- Prompt-local cells --------------------------------------------------- *)

let newCellImpl (label : any) (init : any) (body : any) : any =
  inject
    (Hoop_Runtime_Syntax.NewP (string_of_jsstring label, init, magic body) : comp)

let readCellImpl (label : any) : any =
  inject (Hoop_Runtime_Syntax.ReadP (string_of_jsstring label) : comp)

let writeCellImpl (label : any) (value : any) : any =
  inject (Hoop_Runtime_Syntax.WriteP (string_of_jsstring label, value) : comp)

(* --- Clause and return-clause builders ------------------------------------ *)

(* All three return a function, so all three are built in `hoop_prim.js` -- see
   the note there. An OCaml definition would be flattened by Melange's arity
   optimisation and export the wrong shape. *)
let mkFullClauseImpl (f : any) : any = mk_full_clause f
let mkFastClauseImpl (f : any) : any = mk_fast_clause f
let mkReturnImpl (f : any) : any = mk_return (inject pureImpl) f

(* The identity return clause. `withImpl` tests it with `x == null`. *)
let undefinedReturnImpl : any = inject ()

let emptyClausesImpl (_unit : any) : any = empty_record (inject 0)
let emptyHandlersImpl (_unit : any) : any = empty_record (inject 0)

let insertClauseImpl (key : any) (value : any) (rec_ : any) : any = insert key value rec_
let insertClausesImpl (key : any) (value : any) (rec_ : any) : any = insert key value rec_

(* --- Running -------------------------------------------------------------- *)

(* See the long note in `runtime/ml/hoop_ffi.ml` on why each branch below is
   covered by `Hoop.Runtime.execute`'s (unconditional) theorem, and on what the
   `var_eff` split assumes. Nothing about that reasoning is backend-specific. *)
let runImpl (c : any) : any =
  match Hoop_Runtime.execute apply_full apply_fast (magic c : comp) with
  | Hoop_Runtime.MDone value -> value
  | Hoop_Runtime.MStuck (eff, op) when eff = Hoop_Runtime_Semantics.var_eff ->
      fail
        ("hoop: the prompt-local cell '" ^ op
         ^ "' was read or written outside the scope that created it.\n\
            A cell lives in a stack frame, by value, for exactly as long as the \
            computation its `new` wraps: a handle that outlives that frame -- \
            returned out of the body, or carried by a continuation resumed \
            below the `new` -- names no cell at all.\n\
            The blame is the program's, not the runtime's: `Hoop.Runtime.execute` \
            has no precondition, and it is proved to stop where the reference \
            machine stops, so this is a real escape rather than a lost frame.")
  | Hoop_Runtime.MStuck (eff, op) ->
      fail ("hoop: Unhandled effect operation '" ^ eff ^ "." ^ op ^ "'")
  | Hoop_Runtime.MStep (_, _, _) ->
      fail "hoop: internal error - the machine stopped in a running state"
