/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/walpb/Snapshot__GetIndex.lean`.
-/
module

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

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF) (hG := hG) := by
  intro sp s
  wp_start as Hs
  iunfold walSnapIdTerm at Hs
  icases Hs with ⟨%c, Hs, %hs⟩
  iunfold snapRoC at Hs
  icases Hs with ⟨%pi, %pt, %pc, %Hn, #Hi, Hci, -⟩
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  have hs1 : s.1 = c.index.getD (W64 0) := by rw [← hs]; rfl
  rcases hci : c.index with _ | i
  · rw [hci] at hs1
    iunfold recCell at Hci
    icases Hci with %Hpi
    subst Hpi
    wp_auto
    rw [hs1]; simp only [Option.getD_none, Option.getD_some]
    iapply HΦ
    ipureintro; trivial
  · rw [hci] at hs1
    iunfold recCell at Hci
    ihave %Hn' := typedPointsto_not_null pi _ _ $$ Hci
    simp only [decide_eq_false Hn']
    wp_auto
    rw [hs1]; simp only [Option.getD_none, Option.getD_some]
    iapply HΦ
    ipureintro; trivial

end proof

end EtcdGrove
end Perennial
