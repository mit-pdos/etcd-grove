/-
Port of election_proof/proof_logSliceFromMsgApp.v.
-/
import EtcdGrove.Raft.Spec.logSliceFromMsgApp

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

theorem logSliceFromMsgApp.wp_proof : logSliceFromMsgApp.spec (GF := GF) (hG := hG) := by
  intro p dq m
  wp_start as Hm
  icases typedPointsto_not_null_dup _ _ _ $$ Hm with ⟨Hm, %Hnn⟩
  iStructNamed Hm
  wp_alloc m_ptr as m; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear m
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial
