/-
Port of election_proof/proof_pbEntryID.v.
-/
module

public import Spec.go_etcd_io.raft.v3.pbEntryID
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem pbEntryID.wp_proof
    (wp_Entry_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    pbEntryID.spec (GF := GF) (hG := hG) := by
  intro p dq e
  wp_start as He
  wp_auto
  wp_apply wp_Entry_GetTerm.1 p dq e $$ [$He] as He
  wp_apply wp_Entry_GetIndex.1 p dq e $$ [$He] as He
  unfold entId
  iapply HΦ $$ He

end proof

end EtcdGrove
end Perennial
