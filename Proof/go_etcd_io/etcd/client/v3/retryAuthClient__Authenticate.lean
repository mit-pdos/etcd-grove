/-
Proof of `Spec/go_etcd_io/etcd/client/v3/retryAuthClient__Authenticate.lean` (the auth plan's C1). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.retryAuthClient__Authenticate
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.authClient__Authenticate

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

theorem retryAuthClient.Authenticate.wp_proof
    (wp_authClient_Authenticate : etcdserverpb.authClient.Authenticate.spec (GF := GF) (hG := hG)) :
    retryAuthClient.Authenticate.spec (GF := GF) (hG := hG) := by
  intro rac conn addr Spec Q ctx cd inp m opts vs
  wp_start as ⟨#Hrac, #Hconn, #Hrpc, #Hpre, #Hctx, Hin, #Hopts, #Hok⟩
  iunfold retryAuthAt at Hrac
  icases Hrac with ⟨%ac, #Hac, #Hstub⟩
  wp_auto
  wp_apply wp_authClient_Authenticate ac conn addr Spec Q ctx cd inp m opts vs $$ [Hin]
    as %resp %err Hres
  · iframe #
    iframe
  iapply HΦ
  simp only [pbAuthenticateRequest]
  iexact Hres

end proof

end EtcdGrove
end Perennial
