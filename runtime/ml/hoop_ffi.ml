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

  This file exposes the following to PureScript. Machine constructors:

    pureImpl(value)                      -> comp
    bindImpl(comp, fn)                   -> comp     fn      : (value) => comp
    performImpl(eff, op, evkey, payload) -> comp
    withImpl(ret, handlers, comp)        -> comp     handlers: { [eff]: { [op]: clause } }
    runImpl(comp)                        -> value    ret     : (value) => comp, or nullish
                                                     clause  : (payload[], k) => comp
                                                     k       : (value) => comp

  Clause and return-clause builders, mirroring the TypeScript runtime's ffi.ts:

    mkFullClauseImpl(f)                  -> clause   f : a1 => .. => an => resume => comp
    mkFastClauseImpl(f)                  -> { fun }  f : a1 => .. => an => comp
    mkReturnImpl(f)                      -> ret      f : (value) => value, lifted with Var
    undefinedReturnImpl                  -> undefined, the identity return clause

  `evkey` is accepted and currently discarded: dispatch still scans the stack for
  the innermost prompt. It is threaded through now so that the perform sites need
  not change when Phase 3 (evidence passing) starts consuming it.

  The PS side imports the multi-argument entry points via Fn2 / Fn3 / Fn4 to keep
  invocation uncurried. Functions must not be curried on the OCaml side: jsoo's
  caml_js_wrap_callback re-wraps a returned OCaml function that evaluates to a
  Function, so nesting wrap_callback yields a double-wrapping bug in which the
  inner invocation sees undefined arguments. The builders above sidestep this by
  being plain JS closures rather than wrapped OCaml functions.

  Fast clauses have no runtime support yet: the machine knows only the fully
  controllable path, the tail-resumptive fast path being Phase 4.
  mkFastClauseImpl exists so the PureScript surface can already be written
  against it, and `apply` rejects such a clause with a clear message instead of
  failing obscurely deep inside a call.
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
let is_function_fn = pure_js_expr "(function (x) { return typeof x === 'function' })"
let is_function (x : any) : bool = magic (call1 is_function_fn x)

let apply (clause : any) (payload : any list) (k : any -> comp) : comp =
  (* A fast clause is the object { fun }, not a function. The machine has no
     tail-resumptive path yet, so say so rather than let the call below fail
     with an opaque "is not a function". *)
  if not (is_function clause) then
    throw
      "hoop: this runtime supports fully controllable (ctl) clauses only; \
       tail-resumptive `fast` clauses arrive in Phase 4"
  else
    let arr = array_to_js (Array.of_list payload) in
    let jk = wrap_callback (fun (x : any) -> inject (k x)) in
    magic (call2 clause arr jk)

(* Object.keys returns own enumerable properties only, so nothing inherited
   from Object.prototype can be mistaken for an effect label or an operation. *)
let object_keys_fn = pure_js_expr "Object.keys"
let object_keys (o : any) : any array = array_of_js (call1 object_keys_fn o)

(* Flatten the nested handler table { [eff]: { [op]: clause } } that PureScript
   hands over into the association list Hoop_Runtime works with. Object keys are
   unique per level, so the result never contains a duplicate (eff, op) pair.
   The conversion happens once per Handle, not once per perform. *)
let handlers_of_js (o : any) : (string * string * any) list =
  Array.fold_right
    (fun (eff_key : any) acc ->
       let eff = string_of_jsstring eff_key in
       let ops_obj = js_get o eff_key in
       Array.fold_right
         (fun (op_key : any) acc' ->
            (eff, string_of_jsstring op_key, js_get ops_obj op_key) :: acc')
         (object_keys ops_obj) acc)
    (object_keys o) []

(* --- Functions exposed to PureScript ------------------------------------ *)

let pure_impl (value : any) : any = inject (Hoop_Runtime.Var value : comp)

let bind_impl (c : any) (fn : any) : any =
  inject (Hoop_Runtime.Op (magic c, fun (x : any) -> magic (call1 fn x)) : comp)

let perform_impl (eff : any) (op : any) (evkey : any) (payload : any) : any =
  inject
    (Hoop_Runtime.Perform
       ( string_of_jsstring eff,
         string_of_jsstring op,
         Array.to_list (array_of_js payload) )
      : comp)

let with_impl (ret : any) (handlers : any) (body : any) : any =
  let hs = handlers_of_js handlers in
  let r =
    if is_nullish ret then None
    else Some (fun (x : any) -> (magic (call1 ret x) : comp))
  in
  inject (Hoop_Runtime.Handle (hs, r, magic body) : comp)

(* --- Clause and return-clause builders ----------------------------------- *)

(*
  These are plain JS closures rather than wrapped OCaml functions, for two
  reasons. They only shuffle JS values around, so routing them through OCaml
  would buy nothing; and they are curried, which `caml_js_wrap_callback` cannot
  express without the double-wrapping bug described at the top of this file.

  `applyPayload` feeds a curried PureScript handler each element of the payload
  array in turn. The array's length always equals the operation's arity, since
  the perform site built it with `mkAction` from the same operation signature.
*)
let apply_payload_fn =
  pure_js_expr
    "(function (f, payload) { \
       var g = f; \
       for (var i = 0; i < payload.length; i++) { g = g(payload[i]); } \
       return g; \
     })"

(* A fully controllable clause from a curried PS handler
   `a1 -> ... -> an -> Cont b r o -> Hoop r o`. `Cont` is the machine's own
   resume function, so it is passed on unwrapped. *)
let mk_ctl_clause_impl =
  call1
    (pure_js_expr
       "(function (ap) { \
          return function (f) { \
            return function (payload, resume) { return ap(f, payload)(resume); }; \
          }; \
        })")
    apply_payload_fn

(* A tail-resumptive clause from a curried PS handler
   `a1 -> ... -> an -> Hoop r b`. The shape matches the TypeScript runtime, but
   see `apply` above: this machine cannot consume one yet. *)
let mk_fast_clause_impl =
  call1
    (pure_js_expr
       "(function (ap) { \
          return function (f) { \
            return { fun: function (payload) { return ap(f, payload); } }; \
          }; \
        })")
    apply_payload_fn

(* The return clause is a *pure* function `a -> o` on the PS side; the machine
   expects `(value) => comp`, so lift the result with Var. *)
let mk_return_impl =
  call1
    (pure_js_expr
       "(function (pure) { \
          return function (f) { return function (value) { return pure(f(value)); }; }; \
        })")
    (wrap_callback pure_impl)

(* The identity return clause. `with_impl` tests it with `x == null`. *)
let undefined_return_impl = pure_js_expr "void 0"

(*
  Record building for the erased handler tables.

  The empties hand out a *fresh* object each time, so a table under
  construction is always private to one builder and `insert` may mutate it
  rather than copy. Copying would cost an object per effect and per operation,
  which matters because a handler closing over anything -- an installed `catch`
  closing over its recovery, say -- rebuilds its table on every call.

  Note the null prototype. The TypeScript runtime uses `{}` here and claims a
  computed key makes a name like `__proto__` an own property; that is not so.
  `rec["__proto__"] = v` on an ordinary object invokes the inherited setter and
  reassigns the prototype, so an effect labelled `__proto__` would silently
  corrupt the table instead of being stored in it. With a null prototype there
  is no setter to invoke and the assignment lands as an own property, which is
  also what `Object.keys` in `handlers_of_js` then reports.
*)
let empty_record_impl = pure_js_expr "(function (_unit) { return Object.create(null); })"

let insert_impl =
  pure_js_expr "(function (key, value, rec) { rec[key] = value; return rec; })"

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
  export "withImpl" (wrap_callback with_impl);
  export "runImpl" (wrap_callback run_impl);
  (* Already JS closures -- do not wrap_callback these. *)
  export "mkFullClauseImpl" mk_ctl_clause_impl;
  export "mkFastClauseImpl" mk_fast_clause_impl;
  export "mkReturnImpl" mk_return_impl;
  export "undefinedReturnImpl" undefined_return_impl;
  export "emptyClausesImpl" empty_record_impl;
  export "emptyHandlersImpl" empty_record_impl;
  export "insertClauseImpl" insert_impl;
  export "insertClausesImpl" insert_impl
