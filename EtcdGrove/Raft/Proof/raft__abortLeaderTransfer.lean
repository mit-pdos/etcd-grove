/-
Port of election_proof/proof_raft__abortLeaderTransfer.v.
-/
import EtcdGrove.Raft.Spec.raft__abortLeaderTransfer

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

theorem raft.abortLeaderTransfer.wp_proof :
    raft.abortLeaderTransfer.spec (GF := GF) (hG := hG) := by
  intro cfg r id s
  -- `leadTransferee := None`; `ownRaftPhys` already says it is `0`
  -- (no leader transfer is in scope), so nothing abstract moves.
  wp_start as Hphys
  wp_auto
  wp_apply raft.wp_store_leadTransferee $$ Hphys as Hphys
  iapply HΦ
  iexact Hphys

end proof

end EtcdGrove
end Perennial
