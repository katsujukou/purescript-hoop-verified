module Hoop.Runtime.Test

open Hoop.Runtime



(*
  Hoop.Runtime は値型 v と clause 型 cl にパラメトリックなので、
  テストでは計算可能な具体型を入れて振る舞いを確かめる。
  本番では v := FStar.Dyn.dyn、cl := PS のクロージャになる。
*)

type tv =
  | VI : int -> tv
  | VS : string -> tv
  | VU : tv

let vadd (a b: tv) : tv =
  match a, b with
  | VI x, VI y -> VI (x + y)
  | _, _ -> VU



(* テスト用の clause 言語。実際の clause は PS のクロージャで中身は見えないが、
   マシンはどんな clause に対しても同じ規律で動くはずなので、代表例を並べる *)

noeq
type tcl =
  | CConst : tv -> tcl (* 定数で再開する          … Reader.ask *)
  | CEcho : tcl (* payload[0] で再開する    … Reader.local 的 *)
  | CAbort : tv -> tcl (* 継続を捨てる            … Exception.throw *)
  | CTwice : tcl (* 継続を2回呼ぶ            … multi-shot *)
  (* a で再開し、その結果に b を足す。継続の戻り値を観測する clause *)
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
  steps は GTot なので exec も GTot になる。F* は nullary なトップレベル let に
  GTot を許さないため、各テストは実行結果をトップレベルに束縛せず、
  assert_norm の中に直接埋め込む形で書く（assert_norm の中身は命題、つまり
  ゴースト位置なので GTot の呼び出しがそのまま正規化される）。
  プログラム本体を組み立てる reader などのヘルパは Tot のままでよい。
*)

let exec (c: comp_tree tv tcl) : GTot (state tv tcl) = steps tapply 1000 (load c)

let result (s: state tv tcl) : option tv =
  match s with
  | Done v -> Some v
  | _ -> None



(* ---- 1. 純粋な Op 連鎖 ---- *)

let _ =
  assert_norm
    (result (exec (Op (Var (VI 1)) (fun x -> Op (Var (VI 2)) (fun y -> Var (vadd x y)))))
      == Some (VI 3))



(* ---- 2. 基本的なハンドラ: perform が届く ---- *)

let reader (n: int) (body: comp_tree tv tcl) : comp_tree tv tcl =
  Handle [("Reader", "ask", CConst (VI n))] None body

let _ =
  assert_norm
    (result (exec (reader 42 (Op (Perform "Reader" "ask" []) (fun n -> Var n)))) == Some (VI 42))



(* ---- 3. deep handler: 再開後もハンドラが再設置され、2回目の perform も届く ---- *)

let _ =
  assert_norm
    (result (exec (reader 7
                  (Op (Perform "Reader" "ask" [])
                      (fun a -> Op (Perform "Reader" "ask" []) (fun b -> Var (vadd a b))))))
      == Some (VI 14))



(* ---- 4. 戻り節 (Handle の Var?) が最後に適用される ---- *)

let _ =
  assert_norm
    (result (exec (Handle [("Reader", "ask", CConst (VI 1))]
                  (Some (fun _ -> Var (VS "wrapped")))
                  (Op (Perform "Reader" "ask" []) (fun n -> Var n))))
      == Some (VS "wrapped"))



(* ---- 5. 継続を捨てる clause: 後続も、そのハンドラの戻り節も走らない ---- *)

let _ =
  assert_norm
    (result (exec (Handle [("Exc", "throw", CAbort (VS "boom"))]
                  (Some (fun _ -> Var (VS "should not run")))
                  (Op (Perform "Exc" "throw" []) (fun _ -> Var (VS "should not run either")))))
      == Some (VS "boom"))



(* ---- 6. 入れ子: 内側のハンドラが外側を隠す ---- *)

let _ =
  assert_norm
    (result (exec (reader 1 (reader 2 (Op (Perform "Reader" "ask" []) (fun n -> Var n)))))
      == Some (VI 2))



(* ---- 7. 内側が扱わない作用は外側へ抜ける ---- *)

let _ =
  assert_norm
    (result (exec (reader 1
                  (Handle [("Other", "op", CConst VU)]
                          None
                          (Op (Perform "Reader" "ask" []) (fun n -> Var n)))))
      == Some (VI 1))



(* ---- 8. multi-shot: 捕捉した継続を2回再開できる ---- *)

let _ =
  assert_norm
    (result (exec (Handle [("Amb", "flip", CTwice)]
                  None
                  (Op (Perform "Amb" "flip" []) (fun n -> Var (vadd n (VI 100))))))
      == Some (VI 102))



(* ---- 9. payload が clause に渡る ---- *)

let _ =
  assert_norm
    (result (exec (Handle [("Echo", "say", CEcho)]
                  None
                  (Op (Perform "Echo" "say" [VS "hello"]) (fun s -> Var s))))
      == Some (VS "hello"))



(* ---- 10. 未処理の作用は Stuck になる (TS 版が throw する箇所) ---- *)

let _ = assert_norm (exec (Perform "Nope" "missing" []) == Stuck "Nope" "missing")



(*
  ---- 11-12. TS 側 machine.test.ts の以下2件を移植したもの。
  再開した継続がプロンプトを再設置する結果、`k` の戻り値は
  「戻り節を通り終えた値」になる、という deep handler の要点。

    "deep semantics through the return clause (Var)"
    "continuation after resume: k's result is the value already
     processed by the return clause"
*)

let ret1000:option (tv -> comp_tree tv tcl) = Some (fun v -> Var (vadd v (VI 1000)))



(* 戻り節が最後に一度だけ適用される: 1 + 1000 *)

let _ =
  assert_norm
    (result (exec (Handle [("ask", "ask", CConst (VI 1))] ret1000 (Perform "ask" "ask" [])))
      == Some (VI 1001))



(* k(1) は戻り節を通った 1001 を返し、clause がそれに 100 を足す *)

let _ =
  assert_norm
    (result (exec (Handle [("ask", "ask", CResumeAdd (VI 1) (VI 100))]
                  ret1000
                  (Perform "ask" "ask" [])))
      == Some (VI 1101))