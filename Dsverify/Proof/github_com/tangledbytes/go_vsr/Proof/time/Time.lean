/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/time/Time.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
The proofs of `pkg/time` (Go's `time.Now` and `Time.UnixNano`: Perennial's `time.wp_Now`,
`time.Time.wp_UnixNano`, `Perennial.Proof.time.Link`): `NewReal`, `Time.Now` (a `*Real`), and the `*Timer` methods.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.NewReal.wp_proof : time.NewReal.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  ipureintro
  exact ⟨_, rfl⟩

/-- The package's initialization gives Go's `time`'s (`time.Now` needs it at Perennial 3afd77e35). -/
theorem time.time_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time ⊢
      isPkgInit (PROP := IProp GF) pkg_id.time := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF)
    pkg_id.github_com.tangledbytes.go_vsr.pkg.time).trans ?_
  show iprop(isPkgInit (PROP := IProp GF) pkg_id.time ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.assert ∗ True) ⊢ _
  iintro ⟨#H, -⟩
  iexact H

theorem time.wp_Real_Now (r : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time }}
      (App (Val #(methods (go.GoType.PointerType time.Real.ty) go!"Now" #r)) (Val #()))
    {{ (n : w64), RET #n; True }} := by
  wp_start
  wp_auto
  ihave #Htime := time.time_init $$ Hpkg
  wp_apply _root_.Perennial.time.wp_Now $$ [$Htime] as %tm _
  wp_apply _root_.Perennial.time.Time.wp_UnixNano as %x _
  wp_end

/-- `t.Now()` as the code calls it through the `Time` interface (`MethodResolve`), `t` a
`*Real`. -/
theorem time.wp_Now_resolve (t : GoInterface) (ht : time.isTime t) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time }}
      (App (App (Val (GoInstruction (MethodResolve time.Time.ty go!"Now"))) (Val #t)) (Val #()))
    {{ (n : w64), RET #n; True }} := by
  obtain ⟨r, rfl⟩ := ht
  wp_start
  wp_auto
  wp_apply time.wp_Real_Now
  wp_end

theorem time.NewTimer.wp_proof : time.NewTimer.spec (GF := GF) (hG := hG) := fun t ticks ht => by
  have ht' := ht
  obtain ⟨r, rfl⟩ := ht
  wp_start
  wp_auto
  wp_apply time.wp_Real_Now as %n _
  iapply HΦ
  unfold time.isTimer
  iexists _, _, _, _
  iframe
  ipureintro; exact ht'

theorem time.Timer.Reset.wp_proof : time.Timer.Reset.spec (GF := GF) (hG := hG) := fun tm st => by
  wp_start as Htm
  unfold time.isTimer
  icases Htm with ⟨%start, %ticks, %t, %act, Htm, %ht⟩
  have ht' := ht
  obtain ⟨r, rfl⟩ := ht
  wp_auto
  wp_apply time.wp_Real_Now as %n _
  iapply HΦ
  iexists _, _, _, _
  iframe
  ipureintro; exact ht'

theorem time.Timer.Done.wp_proof : time.Timer.Done.spec (GF := GF) (hG := hG) := fun tm st => by
  wp_start as Htm
  unfold time.isTimer
  icases Htm with ⟨%start, %ticks, %t, %act, Htm, %ht⟩
  have ht' := ht
  obtain ⟨r, rfl⟩ := ht
  wp_auto
  wp_apply time.wp_Real_Now as %n _
  iapply HΦ
  iexists _, _, _, _
  iframe
  ipureintro; exact ht'

theorem time.Timer.SetState.wp_proof : time.Timer.SetState.spec (GF := GF) (hG := hG) := fun tm st st' => by
  wp_start as Htm
  unfold time.isTimer
  icases Htm with ⟨%start, %ticks, %t, %act, Htm, %ht⟩
  wp_auto
  iapply HΦ
  iexists _, _, _, _
  iframe
  ipureintro; exact ht

theorem time.Timer.State.wp_proof : time.Timer.State.spec (GF := GF) (hG := hG) := fun tm st => by
  wp_start as Htm
  unfold time.isTimer
  icases Htm with ⟨%start, %ticks, %t, %act, Htm, %ht⟩
  wp_auto
  cases st with
  | nil =>
    wp_auto
    rw [show decide (GoInterface.nil ≠ GoInterface.nil) = false by simp]
    iapply HΦ
    iexists _, _, _, _
    iframe
    ipureintro; exact ht
  | ok i =>
    wp_auto
    rw [show decide (GoInterface.ok i ≠ GoInterface.nil) = true by simp]
    iapply HΦ
    iexists _, _, _, _
    iframe
    ipureintro; exact ht

end proofs
end Perennial.github_com.tangledbytes.go_vsr.pkg
