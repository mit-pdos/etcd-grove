/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__wakeWaiters.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).wakeWaiters` (R1-wake), and the broadcast idiom's
splitting law the ledger uses.
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Basics

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.ledger

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.ledger.Assumptions]

/-- A pending broadcast channel also gives its persistent `Unknown` view (to hand to a waiter). -/
theorem ownBroadcastChan_pending_unknown (ch : GoChan) (γ : ChanNames) (Q : IProp GF) :
    ownBroadcastChan ch γ Q .Pending ⊢
      ownBroadcastChan ch γ Q .Pending ∗ ownBroadcastChan ch γ Q .Unknown := by
  iintro H
  icases ownBroadcastChan_open _ _ _ _ $$ H with ⟨%γch, #Hint, Hown⟩
  isplitl [Hown]
  · iapply ownBroadcastChan_close _ _ _ _ γch
    iframe Hint Hown
  · iapply ownBroadcastChan_close _ _ _ _ γch
    iframe Hint

/-- `s.wakeWaiters()` (called with the slot's fields exclusively: holding the lock, or on a fresh
slot): closes the wake channel if there is one; the field is `nil` after. -/
theorem Slot.wp_wakeWaiters (s : Loc) (done : Bool) :
    {{ wakeRep (GF := GF) s done }}
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"wakeWaiters")) (Val #()))
    {{ RET #(); structFieldRef Slot go!"wake" s ↦ chan.nil }} := by
  wp_start as Hwk
  unfold wakeRep
  icases Hwk with ⟨%w, Hw, Hor⟩
  wp_auto
  wp_if_destruct
  · -- `w = nil`: nothing to close
    iapply HΦ
    iexact Hw
  · -- `w ≠ nil`: the pending broadcast channel, closed
    icases Hor with (%Hnil | ⟨-, %γw, Hb⟩)
    · exfalso; simp_all
    wp_apply wp_broadcast_chan_close w γw iprop(True) $$ [$Hb] as -
    · imodintro; itrivial
    iapply HΦ
    iexact Hw

end proof
end Perennial.rabia.internal.ledger
