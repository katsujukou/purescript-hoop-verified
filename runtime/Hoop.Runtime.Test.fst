module Hoop.Runtime.Test

friend Hoop.Runtime.Handlers
(* The evidence environment is abstract too, and the differential tests at the
   bottom run it. Same reason: `assert_norm` would stop at the first `lookup`. *)
friend Hoop.Runtime.Env

open Hoop.Runtime.Syntax
open Hoop.Runtime.Semantics
open Hoop.Runtime.Metatheory

module M = Hoop.Runtime



(* Hoop.Runtime.Syntax is parametric in the value type v and the clause type
   cl, so the tests plug in concrete, computable types to observe the actual
   behaviour. In production, v := FStar.Dyn.dyn and cl := a PureScript closure. *)

type tv =
  | VI : int -> tv
  | VS : string -> tv
  | VU : tv
  // Booleans, pairs and lists, so that the prompt-local-state fixtures at the
  // bottom can be written as the figures they are checked against rather than
  // as an encoding of them.
  | VB : bool -> tv
  | VP : tv -> tv -> tv
  | VL : list tv -> tv

let vadd (a b: tv) : tv =
  match a, b with
  | VI x, VI y -> VI (x + y)
  | _, _ -> VU



(* The clause language used by the tests. Real clauses are opaque PureScript
   closures, but the machine follows the same discipline for any clause
   whatsoever, so a few representative ones suffice. *)

noeq
type tcl =
  | CConst : tv -> tcl (* resume with a constant        -- Reader.ask *)
  | CEcho : tcl (* resume with payload[0]        -- Reader.local-ish *)
  | CAbort : tv -> tcl (* drop the continuation         -- Exception.throw *)
  | CTwice : tcl (* invoke the continuation twice -- multi-shot *)
  (* Resume with a, then add b to what comes back. A clause that observes the return
     value of the continuation *)
  | CResumeAdd : tv -> tv -> tcl
  (* Resume once with `False` and once with `True`, collecting the two results
     into a list -- the `choice` handler of the fixtures at the bottom. *)
  | CBoth : tcl

(**
 * The table constructor the *reference* fixtures use.
 *
 * They run at the raw clause type `tcl`, which carries no tag, and the reference
 * machine never asks what kind a clause is -- so the classifier is arbitrary and
 * this one says as much by being constant. The machine fixtures further down do
 * not use it: they run at `M.clause tcl` and go through
 * `M.mk_runtime_handlers`, which fixes the real classifier, so what they
 * exercise is the table the shipped runtime builds.
 *)
let mkh (#cl: Type) (l: list (entry cl)) : handlers cl = mk_handlers (fun _ -> KFull) l

let tapply (c: tcl) (payload: list tv) (k: (tv -> comp_tree tv tcl)) : comp_tree tv tcl =
  match c with
  | CConst v -> k v
  | CEcho ->
    (match payload with
      | x :: _ -> k x
      | [] -> Var VU)
  | CAbort v -> Var v
  | CTwice -> Op (k (VI 1)) (fun _ -> k (VI 2))
  | CResumeAdd a b -> Op (k a) (fun r -> Var (vadd r b))
  | CBoth -> Op (k (VB false)) (fun r1 -> Op (k (VB true)) (fun r2 -> Var (VL [r1; r2])))

(* `steps` is GTot, hence so is `exec`, and F* does not admit GTot for a nullary
   top-level let. No test therefore binds its result at top level; each embeds
   the run directly inside an assert_norm, whose body is a proposition and so a
   ghost position. Helpers that merely build the program under test, such as
   `reader`, may stay in Tot. *)

let exec (c: comp_tree tv tcl) : GTot (state tv tcl) = steps tapply 1000 (load c)

let result (s: state tv tcl) : option tv =
  match s with
  | Done v -> Some v
  | _ -> None



(* ---- 1. A pure chain of Ops ---- *)

let _ =
  assert_norm
    (result (exec (Op (Var (VI 1)) (fun x -> Op (Var (VI 2)) (fun y -> Var (vadd x y)))))
      == Some (VI 3))



(* ---- 2. Basic handler: the perform reaches it ---- *)

let reader (n: int) (body: comp_tree tv tcl) : comp_tree tv tcl =
  Handle (mkh [("Reader", "ask", CConst (VI n))]) None body

let _ =
  assert_norm
    (result (exec (reader 42 (Op (Perform "Reader" "ask" []) (fun n -> Var n)))) == Some (VI 42))



(* ---- 3. Deep handler: the handler is re-installed after resumption, so a second perform reaches it too ---- *)

let _ =
  assert_norm
    (result (exec (reader 7
                  (Op (Perform "Reader" "ask" [])
                      (fun a -> Op (Perform "Reader" "ask" []) (fun b -> Var (vadd a b))))))
      == Some (VI 14))



(* ---- 4. The return clause (the Var? of Handle) is applied last ---- *)

let _ =
  assert_norm
    (result (exec (Handle (mkh [("Reader", "ask", CConst (VI 1))])
                  (Some (fun _ -> Var (VS "wrapped")))
                  (Op (Perform "Reader" "ask" []) (fun n -> Var n))))
      == Some (VS "wrapped"))



(* ---- 5. A clause that drops the continuation: neither the rest of the body nor that handler's return clause runs ---- *)

let _ =
  assert_norm
    (result (exec (Handle (mkh [("Exc", "throw", CAbort (VS "boom"))])
                  (Some (fun _ -> Var (VS "should not run")))
                  (Op (Perform "Exc" "throw" []) (fun _ -> Var (VS "should not run either")))))
      == Some (VS "boom"))



(* ---- 6. Nesting: the inner handler shadows the outer one ---- *)

let _ =
  assert_norm
    (result (exec (reader 1 (reader 2 (Op (Perform "Reader" "ask" []) (fun n -> Var n)))))
      == Some (VI 2))



(* ---- 7. An effect the inner handler does not cover escapes to the outer one ---- *)

let _ =
  assert_norm
    (result (exec (reader 1
                  (Handle (mkh [("Other", "op", CConst VU)])
                          None
                          (Op (Perform "Reader" "ask" []) (fun n -> Var n)))))
      == Some (VI 1))



(* ---- 8. multi-shot: the captured continuation can be resumed twice ---- *)

let _ =
  assert_norm
    (result (exec (Handle (mkh [("Amb", "flip", CTwice)])
                  None
                  (Op (Perform "Amb" "flip" []) (fun n -> Var (vadd n (VI 100))))))
      == Some (VI 102))



(* ---- 9. The payload is passed to the clause ---- *)

let _ =
  assert_norm
    (result (exec (Handle (mkh [("Echo", "say", CEcho)])
                  None
                  (Op (Perform "Echo" "say" [VS "hello"]) (fun s -> Var s))))
      == Some (VS "hello"))



(* ---- 10. An unhandled effect ends up Stuck ---- *)

let _ = assert_norm (exec (Perform "Nope" "missing" []) == Stuck "Nope" "missing")



(*
  ---- 11-12. Deep semantics through the return clause. Since a resumed
  continuation re-installs the prompt, the value `k` returns is the value that
  has already gone through the return clause.
*)

let ret1000:option (tv -> comp_tree tv tcl) = Some (fun v -> Var (vadd v (VI 1000)))



(* The return clause is applied exactly once, at the very end: 1 + 1000 *)

let _ =
  assert_norm
    (result (exec (Handle (mkh [("ask", "ask", CConst (VI 1))]) ret1000 (Perform "ask" "ask" [])))
      == Some (VI 1001))



(* k(1) returns 1001, the value already processed by the return clause, and the clause adds 100 to it *)

let _ =
  assert_norm
    (result (exec (Handle (mkh [("ask", "ask", CResumeAdd (VI 1) (VI 100))])
                  ret1000
                  (Perform "ask" "ask" [])))
      == Some (VI 1101))


(*
  ---- 13-19. The machine that ships, differentially, over full clauses ----

  `Hoop.Runtime.msim` proves that one machine transition is one or two reference
  transitions, so none of this can fail while that proof stands. It is here
  because it exercises what the proof deliberately does not: the evidence
  realisation actually running -- `lookup`, `extend`, `outer` -- on programs
  where resolving to the wrong level is the difference between capturing the
  right frames and capturing one too many.

  The comparison is between whole *states*, through the erasure: `erase_st` of
  where the machine stops must be `Some` of where the reference machine stops. A
  wrong split cannot hide behind a right result.

  These seven were written against an earlier machine, which carried the
  evidence environment beside a reference `state` and agreed with `Semantics`
  state by state. That machine is gone: a fast clause body runs without the
  capture the reference performs, so the two stacks no longer have equal length
  and `erase_st` is what relates them. The programs, the handler tables and the
  expected answers are unchanged; what is restated is the *form* of the
  comparison -- `erase_st q == Some s` in place of `q == s` -- and the clause
  type, which is now tagged. Every entry below is tagged `Full`, so
  `M.desugar taf tafast (Full c) == taf c` and the reference run is the run
  `exec` performs above, one tag thicker.
*)

let tct = M.ct tv tcl

(* The FFI's full interpreter at the tagged clause type: `tapply`'s body, and
   nothing else. *)
let taf (c: tcl) (payload: list tv) (k: tv -> tct) : tct =
  match c with
  | CConst v -> k v
  | CEcho ->
    (match payload with
      | x :: _ -> k x
      | [] -> Var VU)
  | CAbort v -> Var v
  | CTwice -> Op (k (VI 1)) (fun _ -> k (VI 2))
  | CResumeAdd a b -> Op (k a) (fun r -> Var (vadd r b))
  | CBoth -> Op (k (VB false)) (fun r1 -> Op (k (VB true)) (fun r2 -> Var (VL [r1; r2])))

(* No table in 13-19 tags an entry `Fast`, so this is never reached. It must
   still be supplied: the machine takes both interpreters, and which one applies
   is decided by the tag on the entry rather than by the handle. *)
let tafast (c: tcl) (payload: list tv) : tct = Var VU

(* The reference machine, at the desugared reading of the table. *)
let texec (p: tct) : GTot (state tv (M.clause tcl)) =
  steps (M.desugar taf tafast) 1000 (load p)

(* The machine that ships. *)
let texec_m (p: tct) : M.mstate tv tcl = M.msteps taf tafast 1000 (M.mload p)

let mresult (#cl: Type) (q: M.mstate tv cl) : option tv =
  match q with
  | M.MDone v -> Some v
  | _ -> None

let reader_t (n: int) (body: tct) : tct =
  Handle (M.mk_runtime_handlers [("Reader", "ask", M.Full (CConst (VI n)))]) None body



(* 13. A pure chain of Ops -- no prompt, no evidence, but the stack moves *)

let prog_pure: tct =
  Op (Var (VI 1)) (fun x -> Op (Var (VI 2)) (fun y -> Var (vadd x y)))

let _ = assert_norm (M.erase_st (texec_m prog_pure) == Some (texec prog_pure))
let _ = assert_norm (mresult (texec_m prog_pure) == Some (VI 3))



(* 14. Deep handler: the prompt is re-installed, so the evidence for the second
   perform has to be re-derived on the reinstalled segment *)

let prog_deep: tct =
  reader_t 7 (Op (Perform "Reader" "ask" [])
                 (fun a -> Op (Perform "Reader" "ask" []) (fun b -> Var (vadd a b))))

let _ = assert_norm (M.erase_st (texec_m prog_deep) == Some (texec prog_deep))
let _ = assert_norm (mresult (texec_m prog_deep) == Some (VI 14))



(* 15. Shadowing: the environment must resolve to the inner prompt *)

let prog_shadow: tct =
  reader_t 1 (reader_t 2 (Op (Perform "Reader" "ask" []) (fun n -> Var n)))

let _ = assert_norm (M.erase_st (texec_m prog_shadow) == Some (texec prog_shadow))
let _ = assert_norm (mresult (texec_m prog_shadow) == Some (VI 2))



(* 16. Escape: a level that does not bind the key must not intercept it *)

let prog_escape: tct =
  reader_t 1 (Handle (M.mk_runtime_handlers [("Other", "op", M.Full (CConst VU))])
                     None
                     (Op (Perform "Reader" "ask" []) (fun n -> Var n)))

let _ = assert_norm (M.erase_st (texec_m prog_escape) == Some (texec prog_escape))
let _ = assert_norm (mresult (texec_m prog_escape) == Some (VI 1))



(* 17. Multi-shot. The clause resumes twice, and the second resumption happens
   under a stack one frame taller than the first -- the case in which evidence
   frozen at installation time would cut one frame too many. *)

let prog_twice: tct =
  Handle (M.mk_runtime_handlers [("Amb", "flip", M.Full CTwice)])
         None
         (Op (Perform "Amb" "flip" []) (fun n -> Var (vadd n (VI 100))))

let _ = assert_norm (M.erase_st (texec_m prog_twice) == Some (texec prog_twice))
let _ = assert_norm (mresult (texec_m prog_twice) == Some (VI 102))



(* 18. Multi-shot under a nested prompt, so that the segment reinstalled on the
   second resumption carries a prompt of its own and its level is re-derived *)

let prog_twice_nested: tct =
  Handle (M.mk_runtime_handlers [("Amb", "flip", M.Full CTwice)])
         None
         (reader_t 5
           (Op (Perform "Amb" "flip" [])
               (fun n -> Op (Perform "Reader" "ask" []) (fun r -> Var (vadd n r)))))

let _ = assert_norm (M.erase_st (texec_m prog_twice_nested) == Some (texec prog_twice_nested))
let _ = assert_norm (mresult (texec_m prog_twice_nested) == Some (VI 7))



(* 19. An unhandled effect: the environment's `None` and the search's `None`
   must coincide *)

let _ =
  assert_norm
    (texec_m (Perform "Nope" "missing" []) == M.MStuck "Nope" "missing")


(*
  ---- 20-25. The same machine, over tail-resumptive clauses ----

  Same discipline as 13-19, on the part `MEnvF` is for: a fast clause body
  running in place, the environment it runs under, and the `rev`-based loops
  that replace the three structural walks.

  The fuel is the same 1000 on both sides. It need not be: the machine reaches
  its terminal state in *fewer* transitions than the reference, and a terminal
  state is a fixed point of both iterations, so any fuel large enough for the
  reference is large enough for both.
*)

(*
  The clause language of these tests, kept separate from `tcl` so that the
  fixtures above are untouched. Each constructor is read by *both* interpreters
  -- which is exactly what the `Hoop.Runtime.clause` tag is for: the tag on
  the table entry, not the clause handle, decides which reading applies. The
  names say which reading each was written for.
*)
noeq
type fcl =
  | FRet : tv -> fcl (* fast: the operation's result, immediately *)
  | FEcho : fcl (* fast: the operation's result is payload[0] *)
  (* fast, and effectful: the body performs `Reader.ask` and adds. The action
     belongs to the *handler's* context, so it must resolve outside this
     clause's own prompt -- see `fprog_masked`. *)
  | FAsk : tv -> fcl
  (* fast, and effectful in the other direction: the body performs `Amb.flip`,
     which a *full* clause handles, so the capture takes the `MEnvF` with it --
     see `fprog_capture`. *)
  | FFlip : tv -> fcl
  (* fast, and stateful: the body reads the prompt-local cell of this label,
     increments it, and returns the value it read. The cell lives *below* this
     clause's own prompt, so reaching it means walking past the `MEnvF` -- see
     `fprog_cell_masked`. *)
  | FBump : string -> fcl
  | XRet : tv -> fcl (* full: resume with a constant *)
  | XTwice : fcl (* full: resume twice -- multi-shot *)
  | XAbort : tv -> fcl (* full: drop the continuation *)

let fct = M.ct tv fcl

(* The FFI's full interpreter: handed the delimited continuation. *)
let faf (c: fcl) (payload: list tv) (k: tv -> fct) : fct =
  match c with
  | XRet v -> k v
  | XTwice -> Op (k (VI 1)) (fun _ -> k (VI 2))
  | XAbort v -> Var v
  | FRet v -> k v
  | FEcho -> (match payload with x :: _ -> k x | [] -> Var VU)
  | FAsk v -> Op (Perform "Reader" "ask" []) (fun r -> k (vadd r v))
  | FFlip v -> Op (Perform "Amb" "flip" []) (fun r -> k (vadd r v))
  | FBump s -> Op (ReadP s) (fun n -> Op (WriteP s (vadd n (VI 1))) (fun _ -> k n))

(* The FFI's fast interpreter: not handed the continuation, and cannot be. The
   body's value *is* the operation's result. *)
let fafast (c: fcl) (payload: list tv) : fct =
  match c with
  | FRet v -> Var v
  | FEcho -> (match payload with x :: _ -> Var x | [] -> Var VU)
  | FAsk v -> Op (Perform "Reader" "ask" []) (fun r -> Var (vadd r v))
  | FFlip v -> Op (Perform "Amb" "flip" []) (fun r -> Var (vadd r v))
  | FBump s -> Op (ReadP s) (fun n -> Op (WriteP s (vadd n (VI 1))) (fun _ -> Var n))
  | XRet v -> Var v
  | XTwice -> Var (VI 1)
  | XAbort v -> Var v

(* The reference machine, run at the desugared reading of the table. *)
let fexec (p: fct) : GTot (state tv (M.clause fcl)) =
  steps (M.desugar faf fafast) 1000 (load p)

(* The machine that ships. *)
let fexec_m (p: fct) : M.mstate tv fcl = M.msteps faf fafast 1000 (M.mload p)



(* 20. A fast clause dispatches at all, and its body's value is the operation's
   result. Reader.ask, the canonical tail-resumptive operation. *)

let fprog_basic: fct =
  Handle (M.mk_runtime_handlers [("Reader", "ask", M.Fast (FRet (VI 42)))])
         None
         (Op (Perform "Reader" "ask" []) (fun n -> Var n))

let _ = assert_norm (M.erase_st (fexec_m fprog_basic) == Some (fexec fprog_basic))
let _ = assert_norm (mresult (fexec_m fprog_basic) == Some (VI 42))



(* 21. Deep semantics through a fast clause: the prompt is never left, so the
   second perform finds it again. The machine never cut the stack, so
   this is the case in which a wrong `MEnvF` return would show up as a lost
   frame. *)

let fprog_deep: fct =
  Handle (M.mk_runtime_handlers [("Reader", "ask", M.Fast (FRet (VI 7)))])
         None
         (Op (Perform "Reader" "ask" [])
             (fun a -> Op (Perform "Reader" "ask" []) (fun b -> Var (vadd a b))))

let _ = assert_norm (M.erase_st (fexec_m fprog_deep) == Some (fexec fprog_deep))
let _ = assert_norm (mresult (fexec_m fprog_deep) == Some (VI 14))



(* 22. The masking, which is the whole point of `MEnvF` carrying the saved
   environment. `Log.emit`'s fast body performs `Reader.ask`. Between the perform
   site and the `Log` prompt sits a *nearer* `Reader` handler, and the body must
   not see it: a tail-resumptive clause runs in the context its handler was
   installed in. 1005, not 1100. *)

let fprog_masked: fct =
  Handle (M.mk_runtime_handlers [("Reader", "ask", M.Fast (FRet (VI 5)))]) None
    (Handle (M.mk_runtime_handlers [("Log", "emit", M.Fast (FAsk (VI 1000)))]) None
      (Handle (M.mk_runtime_handlers [("Reader", "ask", M.Fast (FRet (VI 100)))]) None
        (Op (Perform "Log" "emit" []) (fun r -> Var r))))

let _ = assert_norm (M.erase_st (fexec_m fprog_masked) == Some (fexec fprog_masked))
let _ = assert_norm (mresult (fexec_m fprog_masked) == Some (VI 1005))



(* 23. Capture across an `MEnvF`, and multi-shot through it. `Log.emit`'s fast
   body performs `Amb.flip`, whose clause is *full* and resumes twice, so the
   split has to jump over the region the `MEnvF` masks and hand the clause a
   segment in which that `MEnvF` has become the `BindF` the reference machine
   has there. Nothing is reinstalled as an `MEnvF` on either resumption -- which
   is what makes the second one safe. *)

let fprog_capture: fct =
  Handle (M.mk_runtime_handlers [("Amb", "flip", M.Full XTwice)]) None
    (Handle (M.mk_runtime_handlers [("Log", "emit", M.Fast (FFlip (VI 0)))]) None
      (Op (Perform "Log" "emit" []) (fun r -> Var (vadd r (VI 100)))))

let _ = assert_norm (M.erase_st (fexec_m fprog_capture) == Some (fexec fprog_capture))
let _ = assert_norm (mresult (fexec_m fprog_capture) == Some (VI 102))



(* 24. Full and fast clauses in the same table, and a full clause that drops the
   continuation from underneath a fast one. *)

let fprog_mixed: fct =
  Handle (M.mk_runtime_handlers [("Exc", "throw", M.Full (XAbort (VS "boom")))]) None
    (Handle (M.mk_runtime_handlers [("Echo", "say", M.Fast FEcho)])
            (Some (fun _ -> Var (VS "should not run")))
      (Op (Perform "Echo" "say" [VS "hello"])
          (fun s -> Op (Perform "Exc" "throw" []) (fun _ -> Var s))))

let _ = assert_norm (M.erase_st (fexec_m fprog_mixed) == Some (fexec fprog_mixed))
let _ = assert_norm (mresult (fexec_m fprog_mixed) == Some (VS "boom"))



(* 25. An unhandled operation: the environment's `None` and the search's `None`
   must coincide on this machine too. *)

let fprog_stuck: fct = Perform "Nope" "missing" []

let _ = assert_norm (M.erase_st (fexec_m fprog_stuck) == Some (fexec fprog_stuck))
let _ = assert_norm (fexec_m fprog_stuck == M.MStuck "Nope" "missing")


(*
  ---- 26-30. Prompt-local state ----

  The two fixtures that discriminate this design from the one it was chosen
  over. Same program --

      b <- choice; set (get + 1); (b, get)

  -- and only the nesting swapped. Measured against Koka 3.2.2:

      choice(state) = [(False,1),(True,1)]   -- state handler INSIDE choice
      state(choice) = [(False,1),(True,2)]   -- state handler OUTSIDE choice

  The mechanism is where the `ParamF` frame ends up relative to the `PromptF`
  the `choice` clause captures at.

    - state INSIDE choice: the cell was installed *after* the prompt, so it is
      part of the captured segment. Every resumption reinstalls the cell at the
      value it was captured with, and each branch counts from 0. This is
      `Hoop.Runtime.Metatheory.set_param_captured`.

    - state OUTSIDE choice: the cell was installed *before* the prompt, so it
      lies below the cut and the capture does not carry it. The first branch's
      write is still there when the second branch runs. This is
      `Hoop.Runtime.Metatheory.set_param_splice`.

  A machine holding the cell behind a cached pointer would give
  [(False,1),(True,2)] for both, and pass typing, progress and the monad laws
  while doing so.
*)

let cell : string = "s"

(* b <- choice.flip; s := s + 1; (b, s) *)
let sbody : comp_tree tv tcl =
  Op (Perform "Choice" "flip" []) (fun b ->
  Op (ReadP cell) (fun n ->
  Op (WriteP cell (vadd n (VI 1))) (fun _ ->
  Op (ReadP cell) (fun n' -> Var (VP b n')))))

let choice_h (c: comp_tree tv tcl) : comp_tree tv tcl =
  Handle (mkh [("Choice", "flip", CBoth)]) None c

let state_h (c: comp_tree tv tcl) : comp_tree tv tcl = NewP cell (VI 0) c


(* 26. choice(state): the state handler INSIDE choice -- per-branch. *)

let prog_choice_state : comp_tree tv tcl = choice_h (state_h sbody)

let _ =
  assert_norm
    (result (exec prog_choice_state)
      == Some (VL [VP (VB false) (VI 1); VP (VB true) (VI 1)]))


(* 27. state(choice): the state handler OUTSIDE choice -- shared. *)

let prog_state_choice : comp_tree tv tcl = state_h (choice_h sbody)

let _ =
  assert_norm
    (result (exec prog_state_choice)
      == Some (VL [VP (VB false) (VI 1); VP (VB true) (VI 2)]))


(*
  28-29. The same two programs on the machine that ships, compared through the
  erasure. A cell is a frame on both sides and `MParamF` erases to `ParamF`
  pointwise, so nothing here can differ -- which is what these check.
*)

let sbody_t : tct =
  Op (Perform "Choice" "flip" []) (fun b ->
  Op (ReadP cell) (fun n ->
  Op (WriteP cell (vadd n (VI 1))) (fun _ ->
  Op (ReadP cell) (fun n' -> Var (VP b n')))))

let choice_h_t (c: tct) : tct =
  Handle (M.mk_runtime_handlers [("Choice", "flip", M.Full CBoth)]) None c

let state_h_t (c: tct) : tct = NewP cell (VI 0) c

let tprog_choice_state : tct = choice_h_t (state_h_t sbody_t)
let tprog_state_choice : tct = state_h_t (choice_h_t sbody_t)

let _ =
  assert_norm
    (M.erase_st (texec_m tprog_choice_state) == Some (texec tprog_choice_state))
let _ =
  assert_norm
    (mresult (texec_m tprog_choice_state)
      == Some (VL [VP (VB false) (VI 1); VP (VB true) (VI 1)]))

let _ =
  assert_norm
    (M.erase_st (texec_m tprog_state_choice) == Some (texec tprog_state_choice))
let _ =
  assert_norm
    (mresult (texec_m tprog_state_choice)
      == Some (VL [VP (VB false) (VI 1); VP (VB true) (VI 2)]))


(*
  30. A cell reached from inside a tail-resumptive clause body, across the
  region its `MEnvF` masks.

  This is the one place where the machine's cell operations are not the
  reference's read off frame for frame: while a fast clause body is in flight,
  the frames between the `MEnvF` and its own prompt are absorbed by the erasure
  into a single `BindF`, so a cell among them is invisible to the reference
  machine -- and `mfind_param` and `mset_param` must jump over them for the same
  reason `msplit` does. Here the cell lives *below* the `Log` prompt, so both
  the read and the write have to make that jump and land beneath it.

  The body reads 10 and writes 11; the continuation then reads 11 back through
  the frames the machine never took apart.
*)

let fprog_cell_masked : fct =
  NewP cell (VI 10)
    (Handle (M.mk_runtime_handlers [("Log", "emit", M.Fast (FBump cell))]) None
      (Op (Perform "Log" "emit" [])
          (fun r -> Op (ReadP cell) (fun n -> Var (VP r n)))))

let _ =
  assert_norm (M.erase_st (fexec_m fprog_cell_masked) == Some (fexec fprog_cell_masked))
let _ = assert_norm (mresult (fexec_m fprog_cell_masked) == Some (VP (VI 10) (VI 11)))


(*
  ---- 31-34. `blocking_effects`, actually run ----

  These check nothing the interface leaves open. The refinement on
  `blocking_effects` already says of *every* table exactly which effects the
  list holds, and the solver discharges all four from it without looking at one
  character of the realisation -- which is what the `--no_smt` below forbids it
  from doing.

  What they buy is that the *executable* form reduces at all. Nothing calls
  `blocking_effects`: the borrowability check belongs to the `Weave` transition,
  which does not exist yet, so esbuild's tree shaking drops it and it is absent
  from `src/Hoop/Engine.js` entirely. Every other definition the runtime
  extracts is exercised by the smoke tests against the shipped bundle; this one
  has no bundle to be exercised in, and until `Weave` lands these four
  `assert_norm`s are the only thing that has ever *run* it.

  Hence `--no_smt`, which fails unless the term reduces to the literal on the
  right, and hence the `friend Hoop.Runtime.Handlers` at the top of this file.
  Without the friendship the normaliser stops at the abstract
  `blocking_effects`, the solver quietly finishes the job from the refinement,
  and every one of these still passes -- as the reading they are not. That was
  checked, in a module that does not friend: `--no_smt` reports the whole
  application unreduced.

  33 and 34 are the pair that earns its place. `blocking_effects` is stated
  through `lookup_handler` and not over the entry list, so a table binding one
  operation twice is judged on the entry that would actually be dispatched --
  Decision 7 of the scoped-effects design note. The two tables differ only in
  which of the two entries comes first, and the answer flips with it: a `Full`
  clause shadowed by a `Fast` one blocks nothing. Nothing else in this suite
  pins that.

  Built with `M.mk_runtime_handlers`, as 13-30 are, so what they run over is the
  table the shipped runtime builds and the kinds are the real classifier's --
  `mkh`'s constant `fun _ -> KFull` would make every table block.
*)

(* 31. Every clause tail-resumptive: nothing blocks. *)

let bh_all_fast : handlers (M.clause tcl) =
  M.mk_runtime_handlers [("Reader", "ask", M.Fast (CConst (VI 1)));
                         ("Log", "emit", M.Fast CEcho)]

(* 32. One full clause among fast ones: its effect, and only its effect. *)

let bh_one_full : handlers (M.clause tcl) =
  M.mk_runtime_handlers [("Reader", "ask", M.Fast (CConst (VI 1)));
                         ("Exc", "throw", M.Full (CAbort (VS "boom")))]

(* 33. The same operation twice, fast first: the `Full` entry is shadowed, so it
   is not dispatchable, so it does not block. *)

let bh_fast_over_full : handlers (M.clause tcl) =
  M.mk_runtime_handlers [("St", "get", M.Fast (CConst (VI 0)));
                         ("St", "get", M.Full (CConst (VI 9)))]

(* 34. The same two entries, swapped: now the `Full` one is what dispatches. *)

let bh_full_over_fast : handlers (M.clause tcl) =
  M.mk_runtime_handlers [("St", "get", M.Full (CConst (VI 9)));
                         ("St", "get", M.Fast (CConst (VI 0)))]

#push-options "--no_smt"
let _ = assert_norm (blocking_effects bh_all_fast == [])
let _ = assert_norm (blocking_effects bh_one_full == ["Exc"])
let _ = assert_norm (blocking_effects bh_fast_over_full == [])
let _ = assert_norm (blocking_effects bh_full_over_fast == ["St"])
#pop-options
