/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/walpb/Snapshot__Clone.lean`: the
receiver is non-nil (`snapRoC_ne`), so `proto.Clone` (`proto.CloneWalSnap.spec`, a
hypothesis) and the type assertion, which holds.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__Clone
public import LinuxFs.Spec.google_golang_org.protobuf.proto.CloneWalSnap

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

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.Clone.wp_proof
    (wp_Clone : proto.CloneWalSnap.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.Clone.spec (GF := GF) (hG := hG) := by
  intro sp s
  wp_start as #Hs
  ihave #Hs2 := Hs
  iunfold walSnapIdTerm at Hs2
  icases Hs2 with ⟨%c, Hs2, %hs⟩
  ihave %Hn := snapRoC_ne sp c $$ Hs2
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  wp_apply wp_Clone sp s $$ [] as %sp' #Hs'
  · iexact Hs
  try wp_auto
  iapply HΦ
  iexact Hs'

end proof

end EtcdGrove
end Perennial
