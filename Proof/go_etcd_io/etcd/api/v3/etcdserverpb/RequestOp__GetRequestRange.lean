/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/RequestOp__GetRequestRange.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RequestOp__GetRequestRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

theorem RequestOp.GetRequestRange.wp_proof : RequestOp.GetRequestRange.spec (GF := GF) (hG := hG) := by
  intro p op
  wp_start as #Hp
  cases op
  case txn cs ts es =>
    iunfold txn.requestOpIs at Hp
    icases Hp with ⟨%Hnn, %w, %r, #Hreq, -⟩
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    · iapply HΦ; ipureintro; rfl
  all_goals
    iunfold txn.requestOpIs at Hp
    icases Hp with ⟨%Hnn, %u, %w, %r, %o', #Hreq, Hc⟩
    icases Hc with (⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩) <;>
      (obtain ⟨Hu, Hop⟩ := Hu; subst Hu) <;>
      (wp_auto; wp_if_destruct; (try exact absurd rfl Hnn)) <;>
      first
      | (cases Hop; done)
      | (wp_auto; iapply HΦ; first | (cases Hop; iexact Hr) | (ipureintro; rfl))
      | (iapply HΦ; first | (cases Hop; iexact Hr) | (ipureintro; rfl) | (rw [← Hop]; simp only [txn.putTxnOp]; split <;> (try split) <;> ipureintro <;> rfl))
      | (exfalso; revert Hop; unfold txn.putTxnOp; split <;> (try split) <;> simp)

end proof

end EtcdGrove
end Perennial
