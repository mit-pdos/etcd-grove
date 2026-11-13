/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/prepareDataWithPadding.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.prepareDataWithPadding
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

theorem go_etcd_io.etcd.server.v3.storage.wal.prepareDataWithPadding.wp_proof
    (wp_efs : go_etcd_io.etcd.server.v3.storage.wal.encodeFrameSize.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.prepareDataWithPadding.spec (GF := GF) (hG := hG) := by
  intro s xs hxs
  wp_start as ⟨Hs, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  have hl : 0 ≤ sint.Z s.len := Hlen.2
  have hn : sint.nat s.len = xs.length := Hlen.1.symm
  wp_apply wp_efs s.len hl
  rw [hn]
  wp_if_destruct
  · have hp := WalEnc.framePad_lt xs.length
    have h0 : WalEnc.framePad xs.length = 0 := by
      have := congrArg BitVec.toNat Hif
      simp only [BitVec.toNat_ofInt] at this
      omega
    simp only [WalEnc.encodeFrameSize, h0, List.replicate_zero, List.append_nil, ne_eq,
      not_true_eq_false, ite_false]
    iapply HΦ
    iframe
    iintro H
    iexact H
  · have hp := WalEnc.framePad_lt xs.length
    have h0 : WalEnc.framePad xs.length ≠ 0 := fun h => Hif (by rw [h]; rfl)
    wp_apply (wp_slice_make2 (V := w8) (W64 (WalEnc.framePad xs.length : Nat))) as %z ⟨Hz, -⟩
    · ipureintro; word
    wp_apply (wp_slice_append_undo (V := w8) s xs z _ (DFrac.own 1)) $$ [Hs Hcap Hz] as %s' ⟨Hs', Hcap', -, Hundo⟩
    · iframe
    have hz : sint.nat (W64 (WalEnc.framePad xs.length : Nat)) = WalEnc.framePad xs.length := by
      simp only [sint.nat]; word
    rw [hz]
    simp only [WalEnc.encodeFrameSize, h0, ne_eq, not_false_eq_true, ite_true]
    wp_auto
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
