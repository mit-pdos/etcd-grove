/-
`cellmint.Main` proved not to panic, from the cell's trust-boundary axioms (`Trusted.lean`).
In Go, `Main` panics (`cellmint_test.go`): the two snapshots read 0 and 5, which disagree.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Trusted
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Assumptions]

/-- **`Main` returns** (does not panic), from the cell's specs. In Go it panics. -/
abbrev Main.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint }}
    (App (Val (@! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Main)) (Val #()))
  {{ RET #(); True }}

theorem Main.wp_proof
    (hNew : cellmint.New.spec (GF := GF) (hG := hG))
    (hLock : cellmint.Lock.spec (GF := GF) (hG := hG))
    (hUnlock : cellmint.Unlock.spec (GF := GF) (hG := hG))
    (hGet : cellmint.Get.spec (GF := GF) (hG := hG))
    (hSet : cellmint.Set.spec (GF := GF) (hG := hG))
    (hSnapshot : cellmint.Snapshot.spec (GF := GF) (hG := hG))
    (hAgree : ∀ (γ : CellNames) (v w : w64),
      ⊢ seen (GF := GF) γ v -∗ seen γ w -∗ ⌜v = w⌝) :
    Main.spec (GF := GF) (hG := hG) := by
  wp_start as Hpkg
  -- c := New()
  wp_apply (hNew) as %c ⟨%γ, #Hinv, Havail⟩
  -- s0 := Snapshot(c)
  wp_apply (hSnapshot c γ) $$ [$Hinv] as %s0 ⟨%v0, %Hv0, #Hseen0⟩
  -- Lock(c)
  wp_apply (hLock c γ) $$ [$Hinv $Havail] as ⟨%v1, Hval⟩
  -- Set(c, 5)
  wp_apply (hSet c γ v1 (W64 5)) $$ [$Hinv $Hval] as Hval
  -- Unlock(c)
  wp_apply (hUnlock c γ (W64 5)) $$ [$Hinv $Hval] as Havail
  -- s1 := Snapshot(c)
  wp_apply (hSnapshot c γ) $$ [$Hinv] as %s1 ⟨%v1', %Hv1, #Hseen1⟩
  -- the two readings agree, so s1 = s0: the panic branch is dead
  icases hAgree γ v0 v1' $$ Hseen0 Hseen1 with %Hag
  subst Hv0 Hv1 Hag
  wp_auto
  iapply HΦ
  itrivial

/-- **`Main` returns, from the cell's axioms themselves**; in Go it panics. -/
theorem Main.wp_axioms : Main.spec (GF := GF) (hG := hG) :=
  Main.wp_proof cellmint.New.wp_proof cellmint.Lock.wp_proof cellmint.Unlock.wp_proof
    cellmint.Get.wp_proof cellmint.Set.wp_proof cellmint.Snapshot.wp_proof cellmint.seen_agree

end proof

#print axioms Main.wp_proof
#print axioms Main.wp_axioms

end EtcdGrove
end Perennial
