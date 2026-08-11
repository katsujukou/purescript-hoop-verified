(**
 * The boundary: the layer where F* stops verifying and starts assuming,
 * against Melange. There was a js_of_ocaml counterpart in
 * `runtime/ml/hoop_ffi.ml`; it was retired when Melange became the only
 * backend, and git history has it.
 *
 * *Why a backend change lands here.* This file is where F* stops verifying and starts
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
 *     carried a leading tag, which is why that build had to copy.
 *
 * Those are the two conversions this runtime crosses most: a payload array per
 * `perform`, and `handlers_of_js` converting every key of every table per
 * `with`.
 *
 * *And what it does not.* `wrap_callback` is gone too, but for a different
 * reason: Melange compiles a top-level `let f a b = ...` to a real two-argument
 * JS function, so the entry points below are directly callable from PureScript
 * and the double-wrapping hazard that `caml_js_wrap_callback` created cannot
 * arise. What Melange does NOT remove is the currying trampoline: applying an
 * unknown closure still goes through `Curry._1`, the counterpart of jsoo's
 * `caml_call1`.
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

(* The four conversions a bytecode-oriented backend has to perform and Melange
   does not. Kept as named identities rather than deleted, so that every place
   a value crosses the representation boundary still says so: the reader sees
   where a JS string becomes an OCaml one, and the fact that it costs nothing
   here is a property of the backend rather than of this file. *)
external string_of_jsstring : any -> string = "%identity"
external jsstring_of_string : string -> any = "%identity"
external array_of_js : any -> any array = "%identity"
external array_to_js : any array -> any = "%identity"

(* --- Property access ------------------------------------------------------ *)

external js_get : any -> any -> any = "" [@@mel.get_index]

(* --- The JavaScript primitives, from ./hoop_prim.js ----------------------- *)

external call1 : any -> any -> any = "call1" [@@mel.module "./hoop_prim.js"]
external call2 : any -> any -> any -> any = "call2" [@@mel.module "./hoop_prim.js"]
external call3 : any -> any -> any -> any -> any = "call3" [@@mel.module "./hoop_prim.js"]
external is_nullish : any -> bool = "isNullish" [@@mel.module "./hoop_prim.js"]
external is_function : any -> bool = "isFunction" [@@mel.module "./hoop_prim.js"]
external throw_error : string -> 'a = "throwError" [@@mel.module "./hoop_prim.js"]
external fast_fun : any -> any = "fastFun" [@@mel.module "./hoop_prim.js"]
external scoped_fun : any -> any = "scopedFun" [@@mel.module "./hoop_prim.js"]
external object_keys : any -> any array = "objectKeys" [@@mel.module "./hoop_prim.js"]
external apply_payload : any -> any -> any = "applyPayload" [@@mel.module "./hoop_prim.js"]
external empty_record : any -> any = "emptyRecord" [@@mel.module "./hoop_prim.js"]
external insert : any -> any -> any -> any = "insert" [@@mel.module "./hoop_prim.js"]

(* The curried builders. Kept in JS because Melange would flatten an OCaml
   definition that returns a function -- see `hoop_prim.js`. *)
external mk_full_clause : any -> any = "mkFullClause" [@@mel.module "./hoop_prim.js"]
external mk_fast_clause : any -> any = "mkFastClause" [@@mel.module "./hoop_prim.js"]
external mk_scoped_clause : any -> any = "mkScopedClause" [@@mel.module "./hoop_prim.js"]
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

(* A scoped clause: `(payload[], weave, resume) => comp`. It is handed the weave
   capability AND the continuation -- the first is what lets it run an inner
   computation under the handlers the perform site could see, the second is what
   lets it resume that site with a value.

   Both cross as OCaml closures of arity one, which under Melange are already
   one-argument JS functions. `weave` is a function ARGUMENT rather than a
   returned function, so PR #1's arity hazard does not apply to it -- that hazard
   is about a boundary function that returns one, which is why
   `mkScopedClauseImpl` is written in JS and this is not.

   THE TRUSTED ITEM LIVES HERE. Nothing on this side can check that the clause
   applies `weave` only to computations drawn from its own rigid inner family;
   that is what the rank-2 quantifier on the PureScript side is for, and what
   `Hoop.Runtime.WellScopedness.apply_scoped_ok` assumes. *)
let apply_scoped (clause : any) (payload : any list) (weave : comp -> comp)
    (k : any -> comp) : comp =
  let arr = array_to_js (Array.of_list payload) in
  let jw = inject (fun (d : any) -> inject (weave (magic d))) in
  let jk = inject (fun (x : any) -> inject (k x)) in
  magic (call3 clause arr jw jk)

(* The discriminator between the three clause shapes, and the only place any of
   them is inspected. `mkFullClauseImpl` produces a JS function;
   `mkFastClauseImpl` produces the object `{ fun }`; `mkScopedClauseImpl`
   produces `{ scoped }`. The three are mutually exclusive, so nothing here has
   to guess. Anything else is a malformed clause and is reported here, by name,
   rather than left to fail as an opaque "is not a function" from inside the
   machine.

   The tag this attaches is what `Hoop_Runtime.classify_runtime_clause` reads,
   and the kind it derives is what the transitions compare the AST node against.
   So "this clause is scoped" is a reading of the shape the surface built, never
   an assertion by this file. *)
let tag_clause (eff : string) (op : string) (c : any) : any Hoop_Runtime.clause =
  if is_function c then Hoop_Runtime.Full c
  else
    let f = fast_fun c in
    if is_nullish f then
      let s = scoped_fun c in
      if is_nullish s then
        fail
          ("hoop: the clause for '" ^ eff ^ "." ^ op
           ^ "' is neither a fully controllable (ctl) clause, a tail-resumptive \
              (fast) one, nor a scoped one")
      else Hoop_Runtime.Scoped s
    else Hoop_Runtime.Fast f

(* Flatten the nested handler table { [eff]: { [op]: clause } } that PureScript
   hands over into the association list Hoop_Runtime_Handlers works with,
   tagging each entry on the way. Object keys are unique per level, so the
   result never contains a duplicate (eff, op) pair. The conversion happens once
   per Handle, not once per perform.

   The table itself is built by Hoop_Runtime.mk_runtime_handlers rather than by
   Hoop_Runtime_Handlers.mk_handlers, which takes a classifier: this boundary
   must not get to say what kind a clause is, or "every clause here is fast"
   would be an assertion rather than a reading of the tag it just attached.

   This is the loop the jsoo build paid `caml_string_of_jsstring` for, once per
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
    (Hoop_Runtime_Syntax.Handle (Hoop_Runtime.mk_runtime_handlers hs, r, magic body)
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

(* NOT YET REACHABLE FROM PURESCRIPT, and deliberately so: the export list in
   scripts/build-runtime.sh does not carry this name, and the AST node a scoped
   perform needs -- `Hoop_Runtime_Syntax.PerformS` -- is not on guard (e)'s
   whitelist either. Both are one-line additions to that script, and they are the
   review artifact for widening the exposed surface; until they are made, the
   scoped path is complete on the verified side and unreachable from the
   surface. *)
let mkScopedClauseImpl (f : any) : any = mk_scoped_clause f

let mkReturnImpl (f : any) : any = mk_return (inject pureImpl) f

(* The identity return clause. `withImpl` tests it with `x == null`. *)
let undefinedReturnImpl : any = inject ()

let emptyClausesImpl (_unit : any) : any = empty_record (inject 0)
let emptyHandlersImpl (_unit : any) : any = empty_record (inject 0)

let insertClauseImpl (key : any) (value : any) (rec_ : any) : any = insert key value rec_
let insertClausesImpl (key : any) (value : any) (rec_ : any) : any = insert key value rec_

(* --- Reporting a boundary rejection ---------------------------------------- *)

(* `Hoop_Runtime.MRejected` is a DIFFERENT failure from `MStuck`, and the two
   messages below exist so that it reads as one.

   `MStuck` says a required dynamic capability is absent: no prompt on the stack
   handles the operation, or no cell frame answers to the label. `MRejected`
   says the opposite -- the operation IS handled and the transition IS defined
   -- and that what could not be guaranteed is the ANSWER-TYPE AGREEMENT the
   PureScript side assumes when it hands a clause across. The advice differs
   accordingly: a stuck run wants a handler installed, a rejected one wants the
   handler that IS installed to be of the right shape, or the handler stack
   between a scope and its owner rearranged. Reporting both as "unhandled
   operation" would send the reader to the wrong place.

   `Hoop.Runtime.mstep` produces one at a dispatch whose node and whose table
   entry disagree about the kind of the operation, and at a `Weave` whose
   prepared segment crosses a prompt that cannot be borrowed. No program the
   PureScript surface can currently build reaches either -- a scoped perform node
   is not exposed -- but the code is live rather than dead, and the messages are
   what a user will read when it is.

   Note that the build compiles with `-w -a`, so a non-exhaustive match compiles
   silently and fails at run time with `Match_failure`: a constructor added to
   `rejection` must be carried into `rejection_message` by hand. See
   docs/study-notes/2026-08-11-scoped-effects-detailed-design.md (Decision 8). *)

(* `String.concat` would pull the stdlib's `Bytes` machinery into the bundle for
   a message nothing prints. Three lines of `^`, which Melange compiles to JS
   `+`, do the whole job. *)
let rec join_labels (xs : string list) : string =
  match xs with
  | [] -> "(none)"
  | [ x ] -> "'" ^ x ^ "'"
  | x :: rest -> "'" ^ x ^ "', " ^ join_labels rest

let show_operation_kind (k : Hoop_Runtime_Semantics.operation_kind) : string =
  match k with
  | Hoop_Runtime_Semantics.KOrdinaryOperation -> "an ordinary (algebraic) operation"
  | Hoop_Runtime_Semantics.KScopedOperation -> "a scoped operation"

let show_clause_kind (k : Hoop_Runtime_Handlers.clause_kind) : string =
  match k with
  | Hoop_Runtime_Handlers.KFull -> "a fully controllable (ctl) clause"
  | Hoop_Runtime_Handlers.KFast -> "a tail-resumptive (fast) clause"
  | Hoop_Runtime_Handlers.KScoped -> "a scoped clause"

let rejection_message (r : Hoop_Runtime_Semantics.rejection) : string =
  match r with
  | Hoop_Runtime_Semantics.ClauseKindMismatch (eff, op, expected, actual) ->
      "hoop: the boundary rejected the dispatch of '" ^ eff ^ "." ^ op
      ^ "': the perform site asks for " ^ show_operation_kind expected
      ^ ", but the handler in scope holds " ^ show_clause_kind actual
      ^ ".\n\
         This is NOT an unhandled operation -- the handler was found. The \
         operation's signature is the single source of truth the perform site \
         and the clause are both derived from, so a mismatch means one of them \
         was built by hand or against a stale signature."
  (* Both halves are printed. The operation comes from the `Weave` node's own
     origin fields: the node carries the NORMALIZED scope plan -- normalization
     being a condition on the segment the machine is to install -- and beside it
     the operation whose dispatch built it, precisely because it may be evaluated
     arbitrarily far from that dispatch, a clause being free to build a woven
     computation and run it later or not at all. So the message can say which
     scope was refused as well as what stood in its way, and both are what the
     reader has to act on. *)
  | Hoop_Runtime_Semantics.UnborrowableScope (eff, op, blocking) ->
      "hoop: the scope of '" ^ eff ^ "." ^ op
      ^ "' could not be entered across non-borrowable handlers: "
      ^ join_labels blocking
      ^ ".\n\
         This is NOT an unhandled operation -- the handler was found. The \
         current implementation can reinstall an intervening prompt only when \
         its clauses are independent of the answer type (fast); a fully \
         controllable one would need the prompt re-instantiated at the scope's \
         result type, which is not supported yet. Either make the listed \
         handlers tail-resumptive, or install them outside the scope rather \
         than between it and its handler."

(* --- Running -------------------------------------------------------------- *)

(*
  `Hoop_Runtime.execute` is the whole machine, and the only entry point this
  file calls: the reference transitions with the stack walk replaced by an
  evidence lookup and with tail-resumptive clauses run in place, proved in F* to
  stop at a state whose erasure `Hoop.Runtime.Semantics.steps` -- the
  stack-walking specification -- reaches on the same program, under the
  reference reading `Hoop.Runtime.desugar` gives this very pair of interpreters.
  Nothing of that specification is extracted; it is ghost throughout, so the
  only thing crossing back is `Hoop_Runtime.mstate`.

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
    the F* side cannot see them doing; what is proved is that if it is reached,
    the blame lies with the program.

    The branch splits in two on the *reserved* effect name
    `Hoop.Runtime.Semantics.var_eff`, which the reference machine reports a
    missing prompt-local cell under: `Stuck var_eff label`. It is always the
    same fault -- a cell handle used outside the scope of the `new` that created
    it -- so it is worth naming as that rather than reporting the useless
    generic message. The constant is READ FROM THE EXTRACTED MODULE rather than
    written out here, so the two cannot drift apart.

    What that split ASSUMES is the reservation itself: that no program performs
    an ordinary operation under the effect label `%hoop.var`, in which case the
    specialised message would be wrong. It is exactly what
    `Hoop.Runtime.WellScopedness.ws` demands of a `Perform` -- `eff =!= var_eff`
    -- so a program the PureScript surface accepts cannot violate it, and one
    that does was already outside the guarded half of the theorem.

  - `MRejected r`. The reference machine reaches `Rejected r` on this program,
    so this too is a report about the *program* rather than a defect of the
    machine. It is a different fault from `MStuck` and is reported as one --
    see the note on `rejection_message` above -- and it is ruled out by a
    different condition: `never_rejected` rather than `never_stuck`.

    Three transitions produce one: a `Perform` whose entry holds a scoped
    clause, a `PerformS` whose entry holds an ordinary one, and a `Weave` whose
    prepared segment crosses a prompt that cannot be borrowed. The first two are
    ruled out by the PureScript surface -- one operation signature derives both
    the perform site and the clause -- and the third by the handler stack a
    program actually installs, which no static discipline in this design decides.
    NEITHER IS VISIBLE FROM INSIDE F*, which is why they are `never_rejected`
    rather than a theorem.

  - `MStep _`. Unreachable, and not by an appeal to well-scopedness: `mrun`
    returns only from its own catch-all, which it enters only on a state that is
    not `MStep`. It is spelled out because `execute`'s return type is `mstate`,
    which has the constructor, and an incomplete match would raise
    `Match_failure` instead of a legible error. Note that the build compiles
    with `-w -a`, so an incomplete match here is not reported: a constructor
    added to `mstate` must be carried into this match by hand.

  `execute` proves one thing more, guarded by two conditions: given
  `never_stuck (desugar apply_full apply_fast) (load c)` -- the well-scopedness
  obligation, which is exactly what PureScript's row types are meant to
  establish and what `apply_ok` assumes of the two closures above -- AND
  `never_rejected` of the same, which is agreement at the typed boundary, the
  result is `MDone` and none of the branches below the first arises. The two are
  separate obligations on separate grounds, and neither implies the other. The
  assumptions are therefore not load-bearing for the answer being *right*; they
  are load-bearing only for the failure branches being unreachable.

  None of this reasoning is backend-specific.
*)
let runImpl (c : any) : any =
  match Hoop_Runtime.execute apply_full apply_fast apply_scoped (magic c : comp) with
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
  | Hoop_Runtime.MRejected r -> fail (rejection_message r)
  | Hoop_Runtime.MStep (_, _, _) ->
      fail "hoop: internal error - the machine stopped in a running state"
