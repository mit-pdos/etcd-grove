/-
Port of election_proof/proof_IsEmptyHardState.v.
-/
module

public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.isHardStateEqual

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

theorem IsEmptyHardState.wp_proof
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG)) :
    IsEmptyHardState.spec (GF := GF) (hG := hG) := by
  intro st
  wp_start
  ihave Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  iNamed Hinit
  wp_auto
  wp_apply wp_isHardStateEqual
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
