/-
Proof of `Spec/go_etcd_io/etcd/client/v3/RetryAuthClient.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.RetryAuthClient
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewAuthClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem RetryAuthClient.wp_proof (wp_NewAuthClient : NewAuthClient.spec (GF := GF) (hG := hG)) :
    RetryAuthClient.spec (GF := GF) (hG := hG) := by
  intro cl conn
  wp_start as #Hconn
  wp_auto
  wp_apply wp_NewAuthClient as %v ⟨%ac, %Hv, #Hcc⟩
  subst Hv
  wp_alloc rac as Hrac
  iStructNamed Hrac
  ipersist ac
  wp_auto
  iapply HΦ
  iexists rac
  isplitl []
  · ipureintro; rfl
  unfold retryAuthAt authStubAt
  iexists ac
  iframe #

end proof

end EtcdGrove
end Perennial
