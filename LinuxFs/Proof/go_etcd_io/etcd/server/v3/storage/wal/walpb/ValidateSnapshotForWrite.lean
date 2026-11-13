/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/walpb/ValidateSnapshotForWrite.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite.wp_proof
    (wp_GetIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF)
      (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite.spec (GF := GF) (hG := hG) := by
  intro sp sm cs hcs
  wp_start as #Hs
  ihave #Hs0 := Hs
  iunfold walSnapAt at Hs
  icases Hs with ⟨%s, #Hsp, #Hi, #Ht, %Hcs⟩
  ihave %Hn := typedPointsto_not_null sp _ _ $$ Hsp
  ihave %Hin := typedPointsto_not_null s.Index' _ _ $$ Hi
  ihave %Htn := typedPointsto_not_null s.Term' _ _ $$ Ht
  iStructNamed Hsp
  wp_auto
  wp_if_destruct
  · exact absurd Hif Hin
  wp_if_destruct
  · exact absurd Hif Htn
  wp_if_destruct
  · -- the conf state nil: the index is 0
    have hi : sm.Index' = W64 0 := by
      rcases hcs with h | h
      · exact h
      · subst h; simp [Hif] at Hcs
    wp_apply (wp_GetIndex sp sm cs) $$ []
    · iexact Hs0
    rw [hi]
    wp_auto
    iapply HΦ
    itrivial
  · iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
