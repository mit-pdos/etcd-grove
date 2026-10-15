/-
Proof of `Spec/go_etcd_io/etcd/client/v3/RetryKVClient.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.RetryKVClient
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewKVClient

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

theorem RetryKVClient.wp_proof (wp_NewKVClient : NewKVClient.spec (GF := GF) (hG := hG)) :
    RetryKVClient.spec (GF := GF) (hG := hG) := by
  intro cl conn
  wp_start as #Hconn
  wp_auto
  wp_apply wp_NewKVClient as %v ⟨%kc, %Hv, #Hcc⟩
  subst Hv
  wp_alloc rkv as Hrkv
  iStructNamed Hrkv
  ipersist kc
  wp_auto
  iapply HΦ
  iexists rkv
  isplitl []
  · ipureintro; rfl
  unfold retryKVAt kvStubAt
  iexists kc
  iframe #

end proof

end EtcdGrove
end Perennial
