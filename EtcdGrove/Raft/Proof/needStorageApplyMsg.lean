/-
Port of `election_proof/proof_needStorageApplyMsg.v` (857d09190).
-/
import EtcdGrove.Raft.Spec.needStorageApplyMsg

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

theorem needStorageApplyMsg.wp_proof : needStorageApplyMsg.spec (GF := GF) (hG := hG) := by
  intro rd
  wp_start as -
  wp_alloc rd_ptr as rd; wp_pures; wp_load; wp_pures; iclear rd
  ispecialize HΦ $$ []
  · itrivial
  iExactEq HΦ
  congr 2 <;> simp

end proof

end EtcdGrove
end Perennial
