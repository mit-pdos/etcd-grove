/-
Proof of `(*bootstrappedWAL).NewConfigChangeEntries()`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedWAL__NewConfigChangeEntries.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__NewConfigChangeEntries

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 0 in
theorem bootstrappedWAL.NewConfigChangeEntries.wp_proof :
    bootstrappedWAL.NewConfigChangeEntries.spec (GF := GF) := by
  intro w dq dqs dqe dqm bw sv hs es ccEnts mv Hlg
  wp_start as Hpre
  iNamed Hpre
  icases typedPointsto_not_null_dup _ _ _ $$ Hwal with ⟨Hwal, %Hwnn⟩
  iStructNamedSuffix Hwal "W"
  icases typedPointsto_not_null_dup _ _ _ $$ Hmeta with ⟨Hmeta, %Hmnn⟩
  iStructNamedSuffix Hmeta "M"
  ihave #Hpkgs : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  ihave #Hpkgr : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  iunfold bootConfChangeEntsOk at Hcc
  icases Hcc with ⟨%nodeIDs, #Hget, #Hcreate⟩
  (try wp_auto)
  wp_apply Hget $$ %bw.lg' %bw.snapshot' %bw.ents' %dqe [Hents] as %ns ⟨Hents, Hns⟩
  · iframe Hsnap Hents
    ipureintro; exact Hlg
  (try wp_auto)
  wp_apply wp_hsPts_GetTerm bw.st' dqs hs $$ [$Hpkgr $Hst] as Hst
  (try wp_auto)
  wp_apply wp_hsPts_GetCommit bw.st' dqs hs $$ [$Hpkgr $Hst] as Hst
  (try wp_auto)
  wp_apply Hcreate $$ %bw.lg' %ns %hs.Term' %hs.Commit' [Hns] as %cs ⟨Hcs, Hcap, %Hcc_props⟩
  · iframe Hns
    ipureintro; exact Hlg
  (try wp_auto)
  ihave Hwal : w ↦{dq} bw $$ [lgW haveWALW wW stW entsW snapshotW meta'W]
  · iapply typedPointsto_combine _ _ _ Hwnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  ihave Hmeta : bw.meta' ↦{dqm} mv $$ [nodeIDM clusterIDM]
  · iapply typedPointsto_combine _ _ _ Hmnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  iapply HΦ
  iframe Hwal Hst Hents Hmeta Hcs Hcap
  ipureintro; exact Hcc_props

end proof

end EtcdGrove
end Perennial
