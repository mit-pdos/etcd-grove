/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/verifyConsistentIndexIsLatest.lean`. Lean-first
(no Rocq counterpart); D22 J4b (2026-10-27).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.verifyConsistentIndexIsLatest
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Verify
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem verifyConsistentIndexIsLatest.wp_proof
    (hV : verify.Verify.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    verifyConsistentIndexIsLatest.spec (GF := GF) (hG := hG) := by
  intro sn sv cindex Hle
  wp_start as #Hsn
  ihave #Hvpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify $$ []
  · iPkgInit
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  iunfold ownSnapM at Hsn
  icases Hsn with ⟨%ds, %pm, %uf, %Hnn, #HD, #Hd, #HM, #Hm, #Hpb⟩
  wp_auto
  wp_apply hV _ _ iprop(snapshot_ptr ↦ sn ∗ cindex_ptr ↦ cindex) $$ [snapshot cindex]
  · isplitl [snapshot cindex]
    · iframe
    iintro ⟨snapshot, cindex⟩
    wp_auto
    wp_apply hGI pm DFrac.discard sv.Metadata' $$ [] as -
    · iframe #
    wp_apply hGI pm DFrac.discard sv.Metadata' $$ [] as -
    · iframe #
    (try wp_auto)
    wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string go.any) as %mref Hmp
    wp_apply (wp_mapInsert (K := GoString) (V := GoInterface) go.string mref _ _ _) $$ [$Hmp] as Hmp
    (try wp_auto)
    wp_apply (wp_mapInsert (K := GoString) (V := GoInterface) go.string mref _ _ _) $$ [$Hmp] as Hmp
    (try wp_auto)
    iexists #mref
    iframe
    ipureintro
    have : decide (uint.Z sv.Metadata'.Index' ≤ uint.Z cindex) = true := decide_eq_true Hle
    simp_all
  iintro -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
