(*
  The boundary between the runtime extracted from F* and PureScript.
  This file alone is handwritten and deliberately subverts the type system (meaning it is part of the TCB).

  Hoop_Runtime_Syntax is parametric over the value type 'v and the clause type 'cl.
  Both are opaque JS values from PureScript, materialized as `any`; since the
  machine never inspects their contents, the pass-through preserves identity.

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

  Clause and return-clause builders:

    mkFullClauseImpl(f)                  -> clause   f : a1 => .. => an => resume => comp
    mkFastClauseImpl(f)                  -> { fun }  f : a1 => .. => an => comp
    mkReturnImpl(f)                      -> ret      f : (value) => value, lifted with Var
    undefinedReturnImpl                  -> undefined, the identity return clause

  A clause reaches the machine TAGGED, as Hoop_Runtime.Full or .Fast, and the
  tag is what decides which of the two interpreters below runs it. The tagging
  happens in `handlers_of_js`, once per `with`, not once per `perform`; the
  discriminator is the shape the two builders produce, a bare JS function for
  `mkFullClauseImpl` against the object `{ fun }` for `mkFastClauseImpl`.
  Deciding it here rather than at dispatch is what lets F* see the distinction:
  `Hoop.Runtime.desugar` reads a `Fast c` entry as the ordinary ctl clause that
  binds the body to the continuation, so the equivalence is a definition in the
  proof rather than an assumption at the boundary.

  `evkey` is accepted and discarded. Dispatch is by evidence, but the machine
  keys its environment on the `(eff, op)` pair rather than on an encoded string
  -- see `Hoop.Runtime.Handlers.key` for why the model does not assume that
  encoding injective. The parameter stays so that the perform sites need not
  change if a realisation ever wants it.

  The PS side imports the multi-argument entry points via Fn2 / Fn3 / Fn4 to keep
  invocation uncurried. Functions must not be curried on the OCaml side: jsoo's
  caml_js_wrap_callback re-wraps a returned OCaml function that evaluates to a
  Function, so nesting wrap_callback yields a double-wrapping bug in which the
  inner invocation sees undefined arguments. The builders above sidestep this by
  being plain JS closures rather than wrapped OCaml functions.
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

(* The machine runs the AST at the TAGGED clause type: an entry of a handler
   table is `Full c` or `Fast c`, never a bare handle. *)
type comp = (any, any) Hoop_Runtime.ct

let call1 (f : any) (a : any) : any = fun_call f [| a |]
let call2 (f : any) (a : any) (b : any) : any = fun_call f [| a; b |]

let nullish_fn = pure_js_expr "(function (x) { return x == null })"
let is_nullish (x : any) : bool = magic (call1 nullish_fn x)

let throw_fn = pure_js_expr "(function (m) { throw new Error(m) })"
let throw (msg : string) : 'a = magic (call1 throw_fn (jsstring_of_string msg))

(* --- The two interpreters the machine dispatches through ------------------ *)

(*
  `Hoop.Runtime.execute` takes both, and the tag on the table entry -- not
  anything either of them inspects -- decides which one runs. Both convert
  OCaml lists and closures into JS arrays and functions to invoke the
  PureScript side.
*)
let is_function_fn = pure_js_expr "(function (x) { return typeof x === 'function' })"
let is_function (x : any) : bool = magic (call1 is_function_fn x)

(* A fully controllable clause: `(payload[], resume) => comp`. The delimited
   continuation is the machine's own, so it is wrapped and handed straight on. *)
let apply_full (clause : any) (payload : any list) (k : any -> comp) : comp =
  let arr = array_to_js (Array.of_list payload) in
  let jk = wrap_callback (fun (x : any) -> inject (k x)) in
  magic (call2 clause arr jk)

(* A tail-resumptive clause: `(payload[]) => comp`. There is no continuation to
   pass, and that is the point -- the body runs in place, under the environment
   the handler was installed in, and its value is the operation's result. The
   handle stored in the `Fast` tag is the `fun` property `handlers_of_js`
   already unwrapped, so no property lookup happens per perform. *)
let apply_fast (clause : any) (payload : any list) : comp =
  magic (call1 clause (array_to_js (Array.of_list payload)))

(* Object.keys returns own enumerable properties only, so nothing inherited
   from Object.prototype can be mistaken for an effect label or an operation. *)
let object_keys_fn = pure_js_expr "Object.keys"
let object_keys (o : any) : any array = array_of_js (call1 object_keys_fn o)

(*
  The discriminator between the two clause shapes, and the only place either is
  inspected. `mkFullClauseImpl` produces a JS function; `mkFastClauseImpl`
  produces the object `{ fun }`. Anything else is a malformed clause -- most
  likely a PureScript record or a plain value that reached the table by a route
  the type checker does not cover -- and is reported here, by name, rather than
  left to fail as an opaque "is not a function" from inside the machine.

  Returns the *inner* function for a fast clause, so that `apply_fast` need not
  reach for `.fun` on every perform.
*)
let fast_fun_fn =
  pure_js_expr
    "(function (x) { \
       return (x !== null && typeof x === 'object' && typeof x.fun === 'function') \
         ? x.fun \
         : null; \
     })"

let tag_clause (eff : string) (op : string) (c : any) : any Hoop_Runtime.clause =
  if is_function c then Hoop_Runtime.Full c
  else
    let f = call1 fast_fun_fn c in
    if is_nullish f then
      throw
        ("hoop: the clause for '" ^ eff ^ "." ^ op
         ^ "' is neither a fully controllable (ctl) clause nor a tail-resumptive \
            (fast) one")
    else Hoop_Runtime.Fast f

(* Flatten the nested handler table { [eff]: { [op]: clause } } that PureScript
   hands over into the association list Hoop_Runtime_Handlers works with,
   tagging each entry on the way. Object keys are unique per level, so the
   result never contains a duplicate (eff, op) pair. The conversion happens once
   per Handle, not once per perform -- which is what makes the tag free at
   dispatch. *)
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

(* --- Functions exposed to PureScript ------------------------------------ *)

let pure_impl (value : any) : any = inject (Hoop_Runtime_Syntax.Var value : comp)

let bind_impl (c : any) (fn : any) : any =
  inject (Hoop_Runtime_Syntax.Op (magic c, fun (x : any) -> magic (call1 fn x)) : comp)

let perform_impl (eff : any) (op : any) (evkey : any) (payload : any) : any =
  inject
    (Hoop_Runtime_Syntax.Perform
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
  (* `mk_handlers` is the only constructor the Handlers interface exposes, and
     where the key cache is derived -- once per Handle. Building the record
     literal here instead would go around the abstraction and break as soon as
     the representation changes. *)
  inject
    (Hoop_Runtime_Syntax.Handle (Hoop_Runtime_Handlers.mk_handlers hs, r, magic body)
      : comp)

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
let mk_full_clause_impl =
  call1
    (pure_js_expr
       "(function (ap) { \
          return function (f) { \
            return function (payload, resume) { return ap(f, payload)(resume); }; \
          }; \
        })")
    apply_payload_fn

(* A tail-resumptive clause from a curried PS handler
   `a1 -> ... -> an -> Hoop r b`. No resume parameter: the body's value is the
   operation's result. The object wrapper is not decoration -- it is the
   discriminator `tag_clause` above tests, the one shape a curried PureScript
   handler cannot be mistaken for. *)
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

  Note the null prototype. On an ordinary `{}`, `rec["__proto__"] = v` invokes
  the inherited setter and reassigns the prototype -- a computed key does *not*
  make it an own property -- so an effect labelled `__proto__` would silently
  corrupt the table instead of being stored in it. With a null prototype there
  is no setter to invoke and the assignment lands as an own property, which is
  what `Object.keys` in `handlers_of_js` then reports.
*)
let empty_record_impl = pure_js_expr "(function (_unit) { return Object.create(null); })"

let insert_impl =
  pure_js_expr "(function (key, value, rec) { rec[key] = value; return rec; })"

(* `Hoop_Runtime.execute` is the whole machine, and the only entry point this
   file calls: the reference transitions with the stack walk replaced by an
   evidence lookup and with tail-resumptive clauses run in place, proved in F*
   to stop at a state whose erasure `Hoop.Runtime.Semantics.steps` -- the
   stack-walking specification -- reaches on the same program, under the
   reference reading `Hoop.Runtime.desugar` gives this very pair of
   interpreters. Nothing of that specification is extracted; it is ghost
   throughout, so the only thing crossing back is `Hoop_Runtime.mstate`.

   That much holds *unconditionally*: `execute` has no precondition, which
   matters here because `c` arrives through `magic` and this file could not
   discharge one. Each branch below is therefore covered by the theorem.

   - `MDone value`. The reference machine reaches `Done value` on this program,
     so `value` is the answer the specification gives.

   - `MStuck (eff, op)`. The reference machine reaches `Stuck (eff, op)` on this
     program -- `steps` walks the stack for a prompt handling `(eff, op)` and
     finds none. The error raised is thus a report about the *program*, not a
     defect of the machine: the operation really is unhandled. This is the one
     branch PureScript's row types are supposed to rule out, and it is the one
     the F* side cannot see them doing; what is now proved is that if it is
     reached, the blame lies with the program.

   - `MStep _`. Unreachable, and not by an appeal to well-scopedness: `mrun`
     returns only from its own catch-all, which it enters only on a state that
     is not `MStep`. It is spelled out because `execute`'s return type is
     `mstate`, which has the constructor, and an incomplete match would raise
     `Match_failure` instead of a legible error.

   `execute` proves one thing more, guarded: given `never_stuck (desugar
   apply_full apply_fast) (load c)` -- the well-scopedness obligation, which is
   exactly what PureScript's row types are meant to establish and what
   `apply_ok` assumes of the two closures above -- the result is `MDone`, so
   the second and third branches do not arise at all. The assumption is
   therefore no longer load-bearing for the answer being *right*; it is
   load-bearing only for `MStuck` being unreachable. *)
let run_impl (c : any) : any =
  match Hoop_Runtime.execute apply_full apply_fast (magic c : comp) with
  | Hoop_Runtime.MDone value -> value
  | Hoop_Runtime.MStuck (eff, op) ->
      throw ("hoop: Unhandled effect operation '" ^ eff ^ "." ^ op ^ "'")
  | Hoop_Runtime.MStep (_, _, _) ->
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
  export "mkFullClauseImpl" mk_full_clause_impl;
  export "mkFastClauseImpl" mk_fast_clause_impl;
  export "mkReturnImpl" mk_return_impl;
  export "undefinedReturnImpl" undefined_return_impl;
  export "emptyClausesImpl" empty_record_impl;
  export "emptyHandlersImpl" empty_record_impl;
  export "insertClauseImpl" insert_impl;
  export "insertClausesImpl" insert_impl
