/-
Port of `election_proof/proof_needStorageApplyRespMsg.v` (857d09190).
-/
import EtcdGrove.Raft.Spec.needStorageApplyRespMsg
import EtcdGrove.Raft.Spec.needStorageApplyMsg

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

theorem needStorageApplyRespMsg.wp_proof
    (wp_needStorageApplyMsg : needStorageApplyMsg.spec (GF := GF) (hG := hG)) :
    needStorageApplyRespMsg.spec (GF := GF) (hG := hG) := by
  intro rd
  wp_start as -
  wp_auto
  wp_apply wp_needStorageApplyMsg
  iapply HΦ
  ipureintro
  trivial

end proof

end EtcdGrove
end Perennial
