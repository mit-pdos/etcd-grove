/-
Tactics for taking a time receipt (`⧗ 1`, Perennial's `GooseLang/Receipts.lean`) from a Go step
(D19b, 2026-10-18). Lean-first (no Rocq counterpart).

`wp_auto` takes every pure step, the resolution of a function or method (`FuncResolve`,
`MethodResolve`) included, and drops its receipt. `wp_take_receipt as Hr` instead steps (pure
steps, loads, stores and allocations of local variables named as `wp_auto` names them, one at a
time) up to the next resolution in evaluation position and takes
that step with `wp_go_step_receipt'`, naming the receipt `Hr`; the WP is then of the resolved
call, which `wp_apply` takes as usual. It fails if a call comes first.
-/
module

public import Perennial.Golang.Theory.Auto
public import Perennial.Golang.Theory.PostLifting
public import Perennial.Golang.Theory.Mem

@[expose] public section

namespace Perennial

set_option hygiene false in
/-- Step (pure steps, loads, stores, allocations) until a `FuncResolve` or `MethodResolve` is in evaluation
position. -/
macro "wp_to_resolve" : tactic => `(tactic|
  repeat (
    fail_if_success wp_bind (App (Val (GoInstruction (FuncResolve _ _))) (Val _))
    fail_if_success wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
    first | wp_pure | wp_load | wp_store | wp_alloc_auto))

set_option hygiene false in
/-- Step to the next function or method resolution and take it, with its time receipt `H`. -/
macro "wp_take_receipt" " as " H:ident : tactic => `(tactic| (
  wp_to_resolve
  first
    | wp_bind (App (Val (GoInstruction (FuncResolve _ _))) (Val _))
    | wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
  iapply wp_go_step_receipt'
  case hv => exact isPanic_intoVal _
  inext
  iintro $H:ident -
  iapply wp_value'))

section preceipt
open Iris Iris.BI Iris.ProgramLogic
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- `wp_go_step_preceipt` with an empty evaluation context (use after `wp_bind`). -/
theorem wp_go_step_preceipt' (i : GoInstruction) (v : val) (e : Expr)
    [go.IsGoStepPureDet i v e] {s : Stuckness} {E : CoPset} (Φ : val → IProp GF) (m : Nat)
    (hv : v.isPanic = false) :
    ⧖ m ∗ ▷ (⧗ 1 -∗ ⧖ (m + 1) -∗ £ 1 -∗ WP e @ s; E {{ Φ }})
    ⊢ WP (App (Val (GoInstruction i)) (Val v)) @ s; E {{ Φ }} :=
  wp_go_step_preceipt i v e Φ [] m hv

end preceipt

set_option hygiene false in
/-- Step to the next function or method resolution and take it, raising the persistent time
receipt `H : ⧖ m` (in the intuitionistic context) to `⧖ (m + 1)`, still named `H` (D19b stage 5,
2026-10-18). -/
macro "wp_raise_receipt" H:ident : tactic => `(tactic| (
  wp_to_resolve
  first
    | wp_bind (App (Val (GoInstruction (FuncResolve _ _))) (Val _))
    | wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
  iapply wp_go_step_preceipt'
  case hv => exact isPanic_intoVal _
  isplitr
  · iexact $H:ident
  iclear $H:ident
  inext
  iintro - #$H:ident -
  iapply wp_value'))

end Perennial
