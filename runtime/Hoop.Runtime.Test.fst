module Hoop.Runtime.Test

open Hoop.Runtime
open Hoop.Runtime.Properties



(*
  Hoop.Runtime is parametric in the value type v and the clause type cl, so the
  tests plug in concrete, computable types to observe the actual behaviour.
  In production, v := FStar.Dyn.dyn and cl := a PureScript closure.
*)

type tv =
  | VI : int -> tv
  | VS : string -> tv
  | VU : tv

let vadd (a b: tv) : tv =
  match a, b with
  | VI x, VI y -> VI (x + y)
  | _, _ -> VU



(* The clause language used by the tests. Real clauses are PureScript closures whose
   bodies are opaque, but the machine is supposed to follow the very same discipline for
   any clause whatsoever, so we line up a few representative ones *)

noeq
type tcl =
  | CConst : tv -> tcl (* resume with a constant        -- Reader.ask *)
  | CEcho : tcl (* resume with payload[0]        -- Reader.local-ish *)
  | CAbort : tv -> tcl (* drop the continuation         -- Exception.throw *)
  | CTwice : tcl (* invoke the continuation twice -- multi-shot *)
  (* Resume with a, then add b to what comes back. A clause that observes the return
     value of the continuation *)
  | CResumeAdd : tv -> tv -> tcl

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

(*
  `steps` is GTot, hence so is `exec`. F* does not admit GTot for a nullary top-level
  let, so no test binds its execution result at top level; each one instead embeds the
  run directly inside an assert_norm (the body of an assert_norm is a proposition, that
  is, a ghost position, so the GTot call is normalized right there).
  Helpers that merely build up the program under test, such as `reader`, may stay in Tot.
*)

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
  Handle [("Reader", "ask", CConst (VI n))] None body

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
    (result (exec (Handle [("Reader", "ask", CConst (VI 1))]
                  (Some (fun _ -> Var (VS "wrapped")))
                  (Op (Perform "Reader" "ask" []) (fun n -> Var n))))
      == Some (VS "wrapped"))



(* ---- 5. A clause that drops the continuation: neither the rest of the body nor that handler's return clause runs ---- *)

let _ =
  assert_norm
    (result (exec (Handle [("Exc", "throw", CAbort (VS "boom"))]
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
                  (Handle [("Other", "op", CConst VU)]
                          None
                          (Op (Perform "Reader" "ask" []) (fun n -> Var n)))))
      == Some (VI 1))



(* ---- 8. multi-shot: the captured continuation can be resumed twice ---- *)

let _ =
  assert_norm
    (result (exec (Handle [("Amb", "flip", CTwice)]
                  None
                  (Op (Perform "Amb" "flip" []) (fun n -> Var (vadd n (VI 100))))))
      == Some (VI 102))



(* ---- 9. The payload is passed to the clause ---- *)

let _ =
  assert_norm
    (result (exec (Handle [("Echo", "say", CEcho)]
                  None
                  (Op (Perform "Echo" "say" [VS "hello"]) (fun s -> Var s))))
      == Some (VS "hello"))



(* ---- 10. An unhandled effect ends up Stuck (where the TS version throws) ---- *)

let _ = assert_norm (exec (Perform "Nope" "missing" []) == Stuck "Nope" "missing")



(*
  ---- 11-12. Ported from the following two cases of machine.test.ts on the TS side.
  Since a resumed continuation re-installs the prompt, the value returned by `k`
  is "the value that has already gone through the return clause" -- the essence of
  deep handlers.

    "deep semantics through the return clause (Var)"
    "continuation after resume: k's result is the value already
     processed by the return clause"
*)

let ret1000:option (tv -> comp_tree tv tcl) = Some (fun v -> Var (vadd v (VI 1000)))



(* The return clause is applied exactly once, at the very end: 1 + 1000 *)

let _ =
  assert_norm
    (result (exec (Handle [("ask", "ask", CConst (VI 1))] ret1000 (Perform "ask" "ask" [])))
      == Some (VI 1001))



(* k(1) returns 1001, the value already processed by the return clause, and the clause adds 100 to it *)

let _ =
  assert_norm
    (result (exec (Handle [("ask", "ask", CResumeAdd (VI 1) (VI 100))]
                  ret1000
                  (Perform "ask" "ask" [])))
      == Some (VI 1101))