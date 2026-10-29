/-
The typed queue's wait group (`Typed.wg`, waited for by `ShutDown` and `ShutDownWithDrain`): no
goroutine is started on a queue without metrics, so its counter stays `0` (`wgInv`), and `Wait`
returns at once. Perennial's `WaitGroup.Wait` spec needs a wait token, whose allocation bounds the
possible waiters below `2^31` (`alloc_wait_token`); each waiter lends one of the queue's
shutdown tokens to `wgInv` for its `Wait` (`shutdownToks`, `shutdownPool` of them), which bounds
them. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `wg.Wait()` on the queue's wait group, with a shutdown token (lent for the call). -/
theorem wp_wgWait (wg : Loc) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup wg γ.wg (wqN.@"wg") ∗
        inv (wqN.@"wginv") (wgInv γ) ∗ shutdownToks γ 1 }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); shutdownToks γ 1 }} := by
  wp_start_folded as ⟨#Hwg, #Hinv, Hst⟩
  -- lend the token and allocate a wait token
  iapply fupd_wp
  iinv Hinv with ⟨%w, >Hctr, >Hw, >Htoks, >Hauth⟩ Hclose
  iunfold shutdownToks at Hst
  icombine Htoks Hst as Htoks
  icombine Hauth Htoks gives %Hle
  imod fupd_mask_subseteq (E1 := ⊤ \ ↑(wqN.@"wginv")) (E2 := ↑(wqN.@"wg"))
    (by solve_ndisj) with Hmask
  imod sync.alloc_wait_token wg γ.wg (wqN.@"wg") (w : Int)
    ⟨by omega, by have := Hle; simp only [shutdownPool] at this; omega⟩ $$ Hwg Hw
    with ⟨Hw, Hwt⟩
  imod Hmask with -
  imod Hclose $$ [Hctr Hw Htoks Hauth] with -
  · inext; iexists w + 1
    rw [show ((w : Int) + 1) = ((w + 1 : Nat) : Int) by omega]
    iframe
  imodintro
  iapply wp_fupd
  wp_apply_core sync.WaitGroup.wp_Wait wg γ.wg (wqN.@"wg") $$ [Hwt] [-]
  · iframe #; iframe
  -- the counter is `0`
  imod inv_acc (E := ⊤ \ ↑(wqN.@"wg")) (sync.wg_mask_ndot_ne wqN "wginv" "wg" (by decide))
    $$ Hinv with ⟨⟨%w1, >Hctr, >Hw, >Htoks, >Hauth⟩, Hclose⟩
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists W32 0
  iframe Hctr
  iintro %_ Hctr
  imod Hmask with -
  imod Hclose $$ [Hctr Hw Htoks Hauth] with -
  · inext; iexists w1; iframe
  imodintro
  iintro Hwt
  -- give the wait token back and take the shutdown token back
  iinv Hinv with ⟨%w2, >Hctr, >Hw, >Htoks, >Hauth⟩ Hclose
  ihave %Hw2 : ⌜w2 ≠ 0⌝ $$ [Hw Hwt]
  · iintro %h; subst h
    iapply sync.waiters_none_token_false $$ Hw Hwt
  imod fupd_mask_subseteq (E1 := ⊤ \ ↑(wqN.@"wginv")) (E2 := ↑(wqN.@"wg"))
    (by solve_ndisj) with Hmask
  imod sync.dealloc_wait_token wg γ.wg (wqN.@"wg") (w2 : Int) (by omega) $$ Hwg Hw Hwt with Hw
  imod Hmask with -
  rw [show w2 = (w2 - 1) + 1 by omega]
  icases ownToks_add_1 1 (w2 - 1) γ.pool $$ Htoks with ⟨Htoks, Hst⟩
  imod Hclose $$ [Hctr Hw Htoks Hauth] with -
  · inext; iexists w2 - 1
    rw [show ((w2 - 1 + 1 : Nat) : Int) - 1 = ((w2 - 1 : Nat) : Int) by omega]
    iframe
  imodintro
  iapply HΦ
  iunfold shutdownToks; iexact Hst

end wps

end workqueue
end EtcdGrove
end Perennial
