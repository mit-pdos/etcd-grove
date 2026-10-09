/-
Port of election_proof/proof_raft__reduceUncommittedSize.v (857d09190).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__reduceUncommittedSize

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

theorem raft.reduceUncommittedSize.wp_proof :
    raft.reduceUncommittedSize.spec (GF := GF) (hG := hG) := by
  intro cfg r id s sz
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply raft.wp_load_uncommittedSize $$ Hphys as %v Hphys
  wp_if_destruct
  · wp_apply raft.wp_store_uncommittedSize $$ Hphys as Hphys
    iapply HΦ $$ Hphys
  · wp_apply raft.wp_load_uncommittedSize $$ Hphys as %v2 Hphys
    wp_apply raft.wp_store_uncommittedSize $$ Hphys as Hphys
    iapply HΦ $$ Hphys

end proof

end EtcdGrove
end Perennial
