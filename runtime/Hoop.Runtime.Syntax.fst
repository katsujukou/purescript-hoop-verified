(**
 * The syntax of a Hoop program: the AST the machines run, and the interface
 * through which handler clauses reach them.
 *
 * The runtime's architecture is that of a CEK-like abstract machine:
 *
 *   - C = Control      ... the current computation node
 *   - E = Environment  ... the evidence environment used for handler dispatch
 *   - K = Kontinuation ... a defunctionalized continuation represented
 *                          as an explicit stack of frames
 *
 * This module holds C and the frames K is built from -- `comp_tree` and
 * `frame`, which are mutually recursive and so cannot be separated. What a
 * machine *does* with them is `Hoop.Runtime.Semantics` (the specification) and
 * `Hoop.Runtime` (the implementation that ships); E belongs to the latter.
 *)
module Hoop.Runtime.Syntax

open FStar.List.Tot

(* The handler table, keyed by (eff, op). `include` rather than `open` so that a
   module opening `Hoop.Runtime.Syntax` sees `handlers`, `lookup_clause`, `keys`
   and `mk_handlers` under the names it always used them by. *)
include Hoop.Runtime.Handlers

(**
 * The `comp_tree` is the C-part of the CEK machine: the AST of the whole
 * program, the chain of `Hoop`-monadic `bind` and `pure` (`Op` and `Var`) plus
 * the effect primitives `handle`/`perform`/`resume`. It is polymorphic in the
 * type `v` of computation inputs/outputs and the type `cl` of handler clauses.
 *
 * `cl` may be understood as something like
 *   ```
 *   list v       -> (v -> comp_tree) -> comp_tree
 *   ^^^^ payloads     ^ continuation
 *  ```
 * but that function type cannot go directly in a constructor argument: doing so
 * violates the [*strictly positive rule.*](https://fstar-lang.org/tutorial/book/part2/part2_inductive_type_families.html#strictly-positive-definitions)
 *)
noeq
type comp_tree (v: Type) (cl: Type) =
  | Op:
      c:comp_tree v cl ->
      fn:(v -> comp_tree v cl) ->
      comp_tree v cl
  | Var:
      value:v ->
      comp_tree v cl
  | Perform:
      eff:string ->
      op:string ->
      payload:list v ->
      comp_tree v cl
  | Handle:
      hs:handlers cl ->
      pure:option (v -> comp_tree v cl) ->
      body:comp_tree v cl ->
      comp_tree v cl
  // `Resumed` node is machine-internal and should never exported to the PS-world;
  // it is inserted by the machine at the head of delimited continuation when it is loaded as
  // the next instruction as the result of firing `continue k` in the handler clause.
  | Resumed:
      frames: list (frame v cl) ->
      value: v ->
      comp_tree v cl

(**
 * A `frame` is the K-part　of the CEK machine and represents a defunctionalized continuation.
 * Basically, it is the right-hand side of a monadic `>>=` chain (making it literally a continuation).
 * Once the program performs an action, control flow jumps to the corresponding handler. 
 * Prompts serve as landmarks for the machine to find the appropriate handlers to process the action.
 *)
and frame (v: Type) (cl: Type) =
  | BindF:
      fn:(v -> comp_tree v cl) ->
      frame v cl
  | PromptF:
      hs:handlers cl ->
      pure:option (v -> comp_tree v cl) ->
      frame v cl

// The clause-monomorphized version of `apply`. This calls a handler clause by feeding
// it the action's payload (`list v`) and the captured delimited continuation.  
// Because clauses are closures passed from the PureScript world via the FFI, F* can 
// guarantee nothing about the invariants enforced by the PS type system. Therefore, 
// we abstract the clause away as a parameter `cl` and specify its invariant 
// via `Hoop.Runtime.WellScopedness.apply_ok`.
let apply_t (v cl : Type) = cl -> list v -> (v -> comp_tree v cl) -> comp_tree v cl
