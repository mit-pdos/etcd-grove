/-
Proof of the spec of the same name (unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isRPCSupportedForLearner

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.isRPCSupportedForLearner.wp_proof :
    v3rpc.isRPCSupportedForLearner.spec (GF := GF) (hG := hG) := by
  intro req
  wp_start as Hl
  iunfold v3rpc.learnerReqOk at Hl
  icases Hl with ⟨%Hreq, #Hser⟩
  rcases Hreq with rfl | ⟨t, l, rfl⟩
  · wp_auto
    iapply HΦ
    itrivial
  · wp_auto
    wp_if_destruct
    · iapply HΦ
      itrivial
    · by_cases ht : t = go.GoType.PointerType etcdserverpb.RangeRequest.ty
      · subst ht
        ihave ⟨%b, #Hb⟩ := Hser $$ %l %rfl
        wp_auto
        iapply HΦ
        itrivial
      · simp only [ht, ite_false, decide_false]
        wp_auto
        iapply HΦ
        itrivial

end proof

end EtcdGrove
end Perennial
