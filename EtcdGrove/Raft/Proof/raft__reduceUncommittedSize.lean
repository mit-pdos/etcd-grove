/-
Port of election_proof/proof_raft__reduceUncommittedSize.v (857d09190).
-/
import EtcdGrove.Raft.Spec.raft__reduceUncommittedSize

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raft.reduceUncommittedSize.wp_proof :
    raft.reduceUncommittedSize.spec (GF := GF) (hG := hG) := by
  intro cfg r id s sz
  wp_start as Hphys
  iNamed Hphys
  wp_alloc r_ptr as r; wp_pures; wp_alloc s_ptr as s; wp_pures; wp_load; wp_load; wp_pures
  wp_apply raft.wp_load_uncommittedSize $$ Hphys as %v Hphys
  wp_pures
  wp_if_destruct
  · wp_load; wp_pures; iclear r s
    wp_apply raft.wp_store_uncommittedSize $$ Hphys as Hphys
    wp_pures
    iapply HΦ $$ Hphys
  · wp_load; wp_pures; wp_load; wp_pures; iclear r
    wp_apply raft.wp_load_uncommittedSize $$ Hphys as %v2 Hphys
    wp_load; wp_pures; iclear s
    wp_apply raft.wp_store_uncommittedSize $$ Hphys as Hphys
    wp_pures
    iapply HΦ $$ Hphys

end proof

end EtcdGrove
end Perennial
