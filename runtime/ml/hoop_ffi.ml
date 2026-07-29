(*
  The boundary between the Hoop_Runtime extracted from F* and PureScript.
  This file alone is handwritten and deliberately subverts the type system (meaning it is part of the TCB).

  Design:
    Hoop_Runtime is parametric over the value type 'v and the clause type 'cl.
    Since both are opaque JS values originating from PureScript, we materialize them as `any`.
    Because the abstract machine never inspects their contents, this allows for identity-preserving pass-throughs.

  We intentionally avoid the standard `js_of_ocaml` library (`Js` module).
  Including it implicitly pulls in `Printf`, `Format`, and `CamlinternalFormat`, 
  which balloons the generated JS to 75KB / 1800 lines. The 12 primitives declared below 
  via `external` are sufficient, keeping the output within 20KB / 400 lines.
  As a trade-off, `ocamlc` requires the `-no-check-prims` flag (as these symbols reside 
  in the jsoo runtime rather than the OCaml bytecode runtime).

  This file exposes multi-argument JS functions:

    pureImpl(value)                     -> comp
    bindImpl(comp, fn)                  -> comp     fn     : (value) => comp
    performImpl(eff, op, payload[])     -> comp
    handleImpl(ret|null, triples, comp) -> comp     triples: Array<[eff, op, clause]>
    runImpl(comp)                       -> value    clause : (payload[], k) => comp
                                                    k      : (value) => comp

  The PS side imports these via `Fn2` / `Fn3` to preserve uncurried invocation.
  Note that functions must not be curried on the OCaml side: jsoo's `caml_js_wrap_callback` 
  automatically re-wraps the return value if it is an OCaml function that evaluates to a Function. 
  Nesting `wrap_callback` results in a double-wrapping bug, where arguments inside the inner 
  invocation resolve to `undefined`.

  The flat array format for `triples` is temporary. The TS-equivalent `Record<eff, Record<op, clause>>` 
  structure and evidence keys will be introduced in Phase 3 (evidence-passing).
*)

(* Opaque JS values. Never inspected from the OCaml side *)
type any

(* --- jsoo runtime primitives (minimal set) ------------------------------ *)

(* OCaml value <-> JS value conversion. Identical representation in jsoo, yielding runtime identities *)
external inject : 'a -> any = "%identity"
external magic : any -> 'a = "%identity"

(* Direct JS expression embedding (restricted to side-effect-free expressions) *)
external pure_js_expr : string -> any = "caml_pure_js_expr"

(* JS function invocation / Wrapping OCaml closures into JS functions *)
external fun_call : any -> any array -> any = "caml_js_fun_call"
external wrap_callback : ('a -> 'b) -> any = "caml_js_wrap_callback"

(* Property and index accessors *)
external js_get : any -> any -> any = "caml_js_get"
external js_set : any -> any -> any -> unit = "caml_js_set"
external int_to_js : int -> any = "%identity"

(* String conversions. Explicit invocation remains safer even with use-js-string=true *)
external jsstring_of_string : string -> any = "caml_jsstring_of_string"
external string_of_jsstring : any -> string = "caml_string_of_jsstring"

(* Array conversions (OCaml arrays in jsoo carry a leading tag, making this a non-identity operation) *)
external array_of_js : any -> any array = "caml_js_to_array"
external array_to_js : any array -> any = "caml_js_from_array"

(* --- Utilities ----------------------------------------------------------- *)

type comp = (any, any) Hoop_Runtime.comp_tree

let call1 (f : any) (a : any) : any = fun_call f [| a |]
let call2 (f : any) (a : any) (b : any) : any = fun_call f [| a; b |]

let nullish_fn = pure_js_expr "(function (x) { return x == null })"
let is_nullish (x : any) : bool = magic (call1 nullish_fn x)

let throw_fn = pure_js_expr "(function (m) { throw new Error(m) })"
let throw (msg : string) : 'a = magic (call1 throw_fn (jsstring_of_string msg))

(*
  Interpretation of clauses dispatched to the abstract machine, mirroring `clause(act.payload, k)` in TS `machine.ts`.
  Converts OCaml lists and closures into JS arrays and functions to invoke the PureScript side.
*)
let apply (clause : any) (payload : any list) (k : any -> comp) : comp =
  let arr = array_to_js (Array.of_list payload) in
  let jk = wrap_callback (fun (x : any) -> inject (k x)) in
  magic (call2 clause arr jk)

let triple_of_js (t : any) : string * string * any =
  ( string_of_jsstring (js_get t (int_to_js 0)),
    string_of_jsstring (js_get t (int_to_js 1)),
    js_get t (int_to_js 2) )

(* --- Functions exposed to PureScript ------------------------------------ *)

let pure_impl (value : any) : any = inject (Hoop_Runtime.Var value : comp)

let bind_impl (c : any) (fn : any) : any =
  inject (Hoop_Runtime.Op (magic c, fun (x : any) -> magic (call1 fn x)) : comp)

let perform_impl (eff : any) (op : any) (payload : any) : any =
  inject
    (Hoop_Runtime.Perform
       ( string_of_jsstring eff,
         string_of_jsstring op,
         Array.to_list (array_of_js payload) )
      : comp)

let handle_impl (ret : any) (triples : any) (body : any) : any =
  let hs = List.map triple_of_js (Array.to_list (array_of_js triples)) in
  let r =
    if is_nullish ret then None
    else Some (fun (x : any) -> (magic (call1 ret x) : comp))
  in
  inject (Hoop_Runtime.Handle (hs, r, magic body) : comp)

let run_impl (c : any) : any =
  match Hoop_Runtime.run apply (Hoop_Runtime.load (magic c : comp)) with
  | Hoop_Runtime.Done value -> value
  | Hoop_Runtime.Stuck (eff, op) ->
      throw ("hoop: Unhandled effect operation '" ^ eff ^ "." ^ op ^ "'")
  | Hoop_Runtime.Step (_, _) ->
      throw "hoop: internal error — the machine stopped in a running state"

(* `jsoo_exports` refers to the object returned by a function wrapped with `--wrap-with-fun`.
   This manually replicates the behavior of `Js.export` from the js_of_ocaml library. *)
let export (name : string) (f : any) : unit =
  js_set (pure_js_expr "jsoo_exports") (jsstring_of_string name) f

let () =
  export "pureImpl" (wrap_callback pure_impl);
  export "bindImpl" (wrap_callback bind_impl);
  export "performImpl" (wrap_callback perform_impl);
  export "handleImpl" (wrap_callback handle_impl);
  export "runImpl" (wrap_callback run_impl)
