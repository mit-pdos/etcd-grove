/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/AuLemmas.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Atomic updates: changing the update's commit and continuation (generic; would belong in
iris-lean's `Iris/BI/Lib/Atomic.lean`).
-/
module

public import Iris.BI.Lib.Atomic

@[expose] public section

namespace Iris.BI

open Iris.Std

section
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {TA TB : Tele}

/-- An atomic update whose commit gives `β1` and continuation `Φ1` is one with commit `β2` and
continuation `Φ2` when `β2` gives `β1` and `Φ1` gives `Φ2`. -/
theorem aupd_mono {Eo Ei : CoPset} {α : TA.Arg → PROP} {β1 β2 Φ1 Φ2 : TA.Arg → TB.Arg → PROP}
    (hβ : ∀ x y, β2 x y ⊢ β1 x y) (hΦ : ∀ x y, Φ1 x y ⊢ Φ2 x y) :
    atomic_update Eo Ei α β1 Φ1 ⊢ atomic_update Eo Ei α β2 Φ2 := by
  refine (and_intro (true_intro (P := atomic_update Eo Ei α β1 Φ1)) .rfl).trans ?_
  refine aupd_intro (P := iprop(True)) ?_
  refine and_elim_r.trans (aupd_aacc.trans ?_)
  unfold atomic_acc
  iintro H
  imod H with ⟨%x, Hα, Hclose⟩
  imodintro
  iexists x
  iframe Hα
  isplit
  · icases Hclose with ⟨Hclose, -⟩
    iexact Hclose
  · icases Hclose with ⟨-, Hclose⟩
    iapply (tforall_forall _).mpr
    iintro %y Hβ
    ihave Hc := (tforall_forall _).mp $$ Hclose
    ispecialize Hc $$ %y
    ihave Hβ1 := hβ x y $$ Hβ
    imod Hc $$ Hβ1 with HΦ
    imodintro
    iapply hΦ x y $$ HΦ

end

end Iris.BI
