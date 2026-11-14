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
  intro Mr sp sm cs hcs
  wp_start as #Hs
  ihave #Hs0 := Hs
  iunfold walSnapAt at Hs
  icases Hs with ⟨%c, Hs, %Hc⟩
  obtain ⟨Hm, Hi, Ht, Hcs, -⟩ := Hc
  iunfold snapRoC at Hs
  icases Hs with ⟨%pi, %pt, %pc, %Hn, #Hpi, Hci, #Hpt, Hct, #Hpc, Hcc, -⟩
  ihave #Hci := recCell_of_eq_some pi Hi $$ Hci
  ihave #Hct := recCell_of_eq_some pt Ht $$ Hct
  ihave %Hcn := walCsOptRoC_null pc c.confState $$ Hcc
  ihave %Hin := typedPointsto_not_null pi _ _ $$ Hci
  ihave %Htn := typedPointsto_not_null pt _ _ $$ Hct
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hin
  wp_if_destruct
  · exact absurd rfl Htn
  wp_if_destruct
  · -- the conf state nil: the index is 0
    have hi : sm.Index' = W64 0 := by
      rcases hcs with h | h
      · exact h
      · have h0 := Hcn.1 rfl
        rw [h0] at Hcs
        exact absurd (h.symm.trans Hcs) (by decide)
    wp_apply (wp_GetIndex sp (sm.Index', sm.Term')) $$ []
    · iapply walSnapAt_idTerm
      iexact Hs0
    rw [hi]
    wp_auto
    iapply HΦ
    itrivial
  · iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
