module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Varint.ReadUvarint
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Varint.PutVarint

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem zigzag_lt (x : w64) : zigzag x < 2 ^ 64 := by
  unfold zigzag sint.Z
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> simp_all <;> omega

/-- `readVarint`'s un-zig-zag: `x := int64(ux >> 1)`, complemented when `ux` is odd. -/
theorem zigzag_unzigzag (u : w64) :
    zigzag (if u &&& W64 1 = W64 0 then u >>> W64 1 else ~~~(u >>> W64 1)) = u.toNat := by
  have hlt := u.isLt
  have hsh : (u >>> W64 1).toNat = u.toNat / 2 := by
    rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight]; simp [W64, Nat.shiftRight_eq_div_pow]
  have hand1 : (u &&& W64 1).toNat = u.toNat % 2 := by
    rw [BitVec.toNat_and, show (W64 1).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hand : (u &&& W64 1 = W64 0) ↔ u.toNat % 2 = 0 := by
    rw [← BitVec.toNat_inj, hand1]; exact Iff.rfl
  by_cases h : u &&& W64 1 = W64 0
  · have h2 := hand.mp h
    simp only [h, ↓reduceIte]
    unfold zigzag sint.Z
    rw [BitVec.toInt_eq_toNat_cond, hsh]
    split <;> simp_all <;> omega
  · have h2 : u.toNat % 2 = 1 := by have := mt hand.mpr h; omega
    simp only [h, ↓reduceIte]
    unfold zigzag sint.Z
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_not, hsh]
    split <;> simp_all <;> omega

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [bufio.Assumptions] [io.Assumptions]
variable [EpBufioDeps GF]

set_option goose.wp.extras true

theorem epaxos.readVarint.spec_holds : epaxos.readVarint.spec (GF := GF) := by
  intro br rd R
  wp_start as ⟨Hown, #Hnext⟩
  ihave #Hnext' := nextIs_shift rd R [] varintEnc (fun _ => True) uvarintEnc (fun n => n < 2 ^ 64)
    (fun v ext t _ h => ⟨zigzag v, ext, zigzag_lt v, by simpa [varintEnc] using h⟩) $$ Hnext
  rw [List.append_nil]
  wp_auto
  wp_apply epaxos.readUvarint.spec_holds br rd R $$ [$Hpkg $Hpkg2 $Hown $Hnext']
    as %u %err Hres
  wp_if_destruct
  · have hz : varintEnc (u >>> W64 1) = uvarintEnc u.toNat := by
      have := zigzag_unzigzag u
      simp only [Hif, ↓reduceIte] at this
      unfold varintEnc; rw [this]
    iapply HΦ
    icases Hres with (⟨%He, Hown⟩ | ⟨%He, Hown⟩)
    · ileft; isplitr
      · ipureintro; exact He
      rw [hz]; iexact Hown
    · iright; isplitr
      · ipureintro; exact He
      iexact Hown
  · have hz : varintEnc (~~~(u >>> W64 1)) = uvarintEnc u.toNat := by
      have := zigzag_unzigzag u
      simp only [Hif, ↓reduceIte] at this
      unfold varintEnc; rw [this]
    iapply HΦ
    icases Hres with (⟨%He, Hown⟩ | ⟨%He, Hown⟩)
    · ileft; isplitr
      · ipureintro; exact He
      rw [hz]; iexact Hown
    · iright; isplitr
      · ipureintro; exact He
      iexact Hown

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
