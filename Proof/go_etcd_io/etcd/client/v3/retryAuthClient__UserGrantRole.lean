/-
Proof of `Spec/go_etcd_io/etcd/client/v3/retryAuthClient__UserGrantRole.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.retryAuthClient__UserGrantRole
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.authClient__UserGrantRole

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

theorem retryAuthClient.UserGrantRole.wp_proof
    (wp_authClient_UserGrantRole : etcdserverpb.authClient.UserGrantRole.spec (GF := GF) (hG := hG)) :
    retryAuthClient.UserGrantRole.spec (GF := GF) (hG := hG) := by
  intro rac conn addr Spec Q ctx cd inp m opts vs
  wp_start as ⟨#Hrac, #Hconn, #Hrpc, #Hpre, #Hctx, Hin, #Hopts, #Hok, %Hsz⟩
  iunfold retryAuthAt at Hrac
  icases Hrac with ⟨%ac, #Hac, #Hstub⟩
  wp_auto
  wp_apply wp_authClient_UserGrantRole ac conn addr Spec Q ctx cd inp m opts vs $$ [Hin] as %resp %err Hres
  · iframe #
    iframe
    try (ipureintro; exact Hsz)
  iapply HΦ
  simp only [pbAuthUserGrantRoleRequest]
  iexact Hres

end proof

end EtcdGrove
end Perennial
