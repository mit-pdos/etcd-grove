/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/encodeFrameSize.lean`: the
translated body.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encodeFrameSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

private theorem srem_nonneg (a b : w64) (ha : 0 ≤ sint.Z a) (hb : 0 < sint.Z b) :
    BitVec.srem a b = W64 (sint.Z a % sint.Z b) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_srem]
  have ha' : a.toInt = sint.Z a := rfl
  have hb' : b.toInt = sint.Z b := rfl
  rw [ha', hb', Int.tmod_eq_emod_of_nonneg ha]
  have h0 : 0 ≤ sint.Z a % sint.Z b := Int.emod_nonneg _ (by omega)
  have h3 : sint.Z a % sint.Z b < sint.Z b := Int.emod_lt_of_pos _ hb
  have : sint.Z b < 2 ^ 63 := by word
  word

/-- Go's `(8 - n%8) % 8` on a non-negative `int` is `framePad`. -/
private theorem pad_eq (n : w64) (hn : 0 ≤ sint.Z n) :
    BitVec.srem (W64 8 - BitVec.srem n (W64 8)) (W64 8) = W64 (WalEnc.framePad (sint.nat n)) := by
  have h8 : sint.Z (W64 8) = 8 := by decide
  rw [srem_nonneg n (W64 8) hn (by rw [h8]; decide), h8]
  have hr0 : 0 ≤ sint.Z n % 8 := Int.emod_nonneg _ (by decide)
  have hr1 : sint.Z n % 8 < 8 := Int.emod_lt_of_pos _ (by decide)
  have hs : sint.Z (W64 8 - W64 (sint.Z n % 8)) = 8 - sint.Z n % 8 := by word
  rw [srem_nonneg _ (W64 8) (by rw [hs]; omega) (by rw [h8]; decide), hs, h8]
  unfold WalEnc.framePad
  have hnat : (sint.nat n : Int) = sint.Z n := Int.toNat_of_nonneg hn
  congr 1
  omega

private theorem len_eq (n : w64) (hn : 0 ≤ sint.Z n) : n = BitVec.ofNat 64 (sint.nat n) := by
  have hnat : (sint.nat n : Int) = sint.Z n := Int.toNat_of_nonneg hn
  word

theorem go_etcd_io.etcd.server.v3.storage.wal.encodeFrameSize.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.encodeFrameSize.spec (GF := GF) (hG := hG) := by
  intro n hn
  wp_start as -
  wp_auto
  rw [pad_eq n hn]
  have hp := WalEnc.framePad_lt (sint.nat n)
  wp_if_destruct
  · have h0 : WalEnc.framePad (sint.nat n) = 0 := by
      have := congrArg BitVec.toNat Hif
      simp only [BitVec.toNat_ofInt] at this
      omega
    have he : (WalEnc.encodeFrameSize (sint.nat n)).1 = n := by
      unfold WalEnc.encodeFrameSize
      simp only [h0, ne_eq, not_true_eq_false, ite_false]
      exact (len_eq n hn).symm
    rw [he]
    iapply HΦ
    itrivial
  · have he : (WalEnc.encodeFrameSize (sint.nat n)).1 =
        n ||| (W64 128 ||| W64 (WalEnc.framePad (sint.nat n) : Nat)) <<< W64 56 := by
      have h0 : WalEnc.framePad (sint.nat n) ≠ 0 := fun h => Hif (by rw [h]; rfl)
      unfold WalEnc.encodeFrameSize
      simp only [h0, ne_eq, not_false_eq_true, ite_true]
      have hpad : W64 (WalEnc.framePad (sint.nat n) : Nat) =
          BitVec.ofNat 64 (WalEnc.framePad (sint.nat n)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
        omega
      rw [hpad, BitVec.shiftLeft_eq', ← len_eq n hn]
      rfl
    rw [he]
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
