module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Varint.PutUvarint

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem shl1_toNat (x : w64) : (x <<< W64 1).toNat = 2 * x.toNat % 2 ^ 64 := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  simp [W64, Nat.shiftLeft_eq, Nat.mul_comm]

/-- `uint64(x) << 1` for `x ≥ 0`. -/
theorem zigzag_nonneg (x : w64) (h : 0 ≤ sint.Z x) : (x <<< W64 1).toNat = zigzag x := by
  unfold zigzag
  unfold sint.Z at h ⊢
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  rw [shl1_toNat]
  split at h <;> simp_all <;> omega

/-- `^(uint64(x) << 1)` for `x < 0`. -/
theorem zigzag_neg (x : w64) (h : sint.Z x < 0) : (~~~(x <<< W64 1)).toNat = zigzag x := by
  unfold zigzag
  unfold sint.Z at h ⊢
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  have hlt := x.isLt
  rw [BitVec.toNat_not, shl1_toNat]
  split at h <;> simp_all <;> omega

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions]

set_option goose.wp.extras true

theorem epaxos.putVarint.spec_holds : epaxos.putVarint.spec (GF := GF) := by
  intro buf bs x
  wp_start as ⟨%Hl, Hb⟩
  wp_auto
  wp_if_destruct
  · rw [show sint.Z (W64 0) = 0 from rfl] at Hif
    have hz : varintEnc x = uvarintEnc (~~~(x <<< W64 1)).toNat := by
      rw [zigzag_neg x Hif]; rfl
    rw [hz] at Hl ⊢
    wp_apply epaxos.putUvarint.spec_holds buf bs _ $$ [$Hpkg $Hb] as Hb
    · ipureintro; exact Hl
    iapply HΦ $$ Hb
  · rw [show sint.Z (W64 0) = 0 from rfl] at Hif
    have hz : varintEnc x = uvarintEnc (x <<< W64 1).toNat := by
      rw [zigzag_nonneg x (by omega)]; rfl
    rw [hz] at Hl ⊢
    wp_apply epaxos.putUvarint.spec_holds buf bs _ $$ [$Hpkg $Hb] as Hb
    · ipureintro; exact Hl
    iapply HΦ $$ Hb

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
