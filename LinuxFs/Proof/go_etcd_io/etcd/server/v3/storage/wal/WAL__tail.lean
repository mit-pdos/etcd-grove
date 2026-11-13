/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__tail.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail

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

theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG) := by
  intro w locks ls lt dq1 dq2
  wp_start as ⟨Hf, Hs⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  obtain ⟨Hl1, Hl2⟩ := Hl
  simp only [List.length_append, List.length_singleton] at Hl1
  wp_if_destruct
  · have hsub : sint.Z (locks.len - W64 1) = sint.Z locks.len - 1 := by word
    have hz : sint.Z locks.len = (ls.length : Int) + 1 := by
      have h3 : (sint.nat locks.len : Int) = sint.Z locks.len := Int.toNat_of_nonneg Hl2
      omega
    have hb : 0 ≤ sint.Z (locks.len - W64 1) ∧ sint.Z (locks.len - W64 1) < sint.Z locks.len := by
      rw [hsub]; omega
    simp only [hb, and_self, ite_true]
    have hidx : (ls ++ [lt])[(sint.Z (locks.len - W64 1)).toNat]? = some lt := by
      have : (sint.Z (locks.len - W64 1)).toNat = ls.length := by rw [hsub, hz]; omega
      rw [this]; simp
    wp_apply (wp_load_slice_index locks (sint.Z (locks.len - W64 1)) (ls ++ [lt]) dq2 lt hb.1)
      $$ [Hs] as Hs
    · iframe; ipureintro; exact hidx
    iapply HΦ
    iframe
  · exfalso; apply Hif
    have h3 : (sint.nat locks.len : Int) = sint.Z locks.len := Int.toNat_of_nonneg Hl2
    rw [show sint.Z (W64 0) = 0 by rfl]; omega

end proof

end EtcdGrove
end Perennial
