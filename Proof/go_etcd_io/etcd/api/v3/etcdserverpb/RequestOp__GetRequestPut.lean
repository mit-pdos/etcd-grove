/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/RequestOp__GetRequestPut.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RequestOp__GetRequestPut

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

theorem RequestOp.GetRequestPut.wp_proof : RequestOp.GetRequestPut.spec (GF := GF) (hG := hG) := by
  intro p op
  wp_start as #Hp
  cases op
  case txn cs ts es =>
    iunfold txn.requestOpIs at Hp
    icases Hp with ⟨%Hnn, %w, %r, #Hreq, -⟩
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    · iapply HΦ; iright; ipureintro
      refine ⟨rfl, fun o h => ?_⟩
      revert h; unfold txn.putTxnOp; (repeat' split) <;> simp
  all_goals
    iunfold txn.requestOpIs at Hp
    icases Hp with ⟨%Hnn, %u, %w, %r, %o', #Hreq, Hc⟩
    icases Hc with (⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩) <;>
      (obtain ⟨Hu, Hop⟩ := Hu; subst Hu) <;>
      (wp_auto; wp_if_destruct; (try exact absurd rfl Hnn)) <;>
      (try wp_auto) <;>
      first
      | (exfalso; revert Hop; unfold txn.putTxnOp; (repeat' split) <;> simp; done)
      | (iapply HΦ; ileft; iexists o'; iframe Hr; ipureintro; exact Hop)
      | (iapply HΦ; iright; ipureintro
         refine ⟨rfl, fun o h => ?_⟩
         revert Hop h; unfold txn.putTxnOp; (repeat' split) <;> simp)

end proof

end EtcdGrove
end Perennial
