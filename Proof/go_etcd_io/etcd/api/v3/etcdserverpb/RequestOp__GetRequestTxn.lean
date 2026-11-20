/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/RequestOp__GetRequestTxn.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RequestOp__GetRequestTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

theorem RequestOp.GetRequestTxn.wp_proof : RequestOp.GetRequestTxn.spec (GF := GF) (hG := hG) := by
  intro p op
  wp_start as #Hp
  cases op
  case txn cs ts es =>
    iunfold txn.requestOpIs at Hp
    icases Hp with ⟨%Hnn, %w, %r, #Hreq, #Hrt, %Hrnn, #Hf⟩
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    · wp_auto
      iapply HΦ
      iunfold txn.txnFieldsIs
      iframe Hf
      ipureintro; exact Hrnn
  all_goals
    iunfold txn.requestOpIs at Hp
    icases Hp with ⟨%Hnn, %u, %w, %r, %o', #Hreq, Hc⟩
    icases Hc with (⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩) <;>
      (obtain ⟨Hu, Hop⟩ := Hu; subst Hu) <;>
      (wp_auto; wp_if_destruct; (try exact absurd rfl Hnn)) <;>
      (try wp_auto) <;>
      (iapply HΦ; ipureintro; rfl)

end proof

end EtcdGrove
end Perennial
