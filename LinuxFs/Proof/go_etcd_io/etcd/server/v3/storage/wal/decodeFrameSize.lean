/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decodeFrameSize.lean`: the
translated body.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decodeFrameSize

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

theorem go_etcd_io.etcd.server.v3.storage.wal.decodeFrameSize.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.decodeFrameSize.spec (GF := GF) (hG := hG) := by
  intro l
  wp_start as -
  wp_auto
  have h1 : W64 ↑(WalEnc.decodeFrameSize l).1 = l &&& ~~~(W64 255 <<< W64 56) := by
    simp only [WalEnc.decodeFrameSize]
    apply BitVec.eq_of_toNat_eq
    simp
  wp_if_destruct
  · have h2 : W64 ↑(WalEnc.decodeFrameSize l).2 = (l >>> W64 56) &&& W64 7 := by
      simp only [WalEnc.decodeFrameSize]
      rw [ite_eq_left (by rw [BitVec.slt_iff_toInt_lt]; word)]
      apply BitVec.eq_of_toNat_eq
      simp
      have h3 : BitVec.toNat l >>> 56 < 18446744073709551616 :=
        Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) l.isLt
      rw [Nat.mod_eq_of_lt h3]
    rw [h1, h2]
    iapply HΦ
    itrivial
  · have h2 : W64 ↑(WalEnc.decodeFrameSize l).2 = 0 := by
      simp only [WalEnc.decodeFrameSize]
      rw [ite_eq_right (by rw [BitVec.slt_iff_toInt_lt]; word)]
      rfl
    rw [h1, h2]
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
