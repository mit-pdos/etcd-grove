/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewAuth.lean` (the auth plan's E2h; a trust-boundary
axiom of item 5 before). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewAuth
public import Spec.go_etcd_io.etcd.client.v3.RetryAuthClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem NewAuth.wp_proof (wp_RetryAuthClient : RetryAuthClient.spec (GF := GF) (hG := hG)) :
    NewAuth.spec (GF := GF) (hG := hG) := by
  intro cl conn
  wp_start as #Hcl
  iunfold clientKVAtS at Hcl
  icases Hcl with ⟨%Hne, %sl, #Hconn, #Hcopts, #Hok⟩
  wp_auto
  wp_apply wp_RetryAuthClient cl conn $$ [] as %v ⟨%rac, %Hv, #Hrac⟩
  · iexact Hconn
  subst Hv
  iStructNamed «$r0»
  ipersist remote
  simp only [decide_eq_false Hne]
  iapply wp_fupd
  wp_auto
  ipersist callOpts
  imodintro
  iapply HΦ
  iexists _
  isplitl []
  · ipureintro; rfl
  unfold authObjS
  iexists rac, sl
  iframe #

end proof

end EtcdGrove
end Perennial
