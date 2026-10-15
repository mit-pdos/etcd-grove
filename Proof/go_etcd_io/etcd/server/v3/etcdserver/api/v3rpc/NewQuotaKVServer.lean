/-
Proof of the spec of the same name (unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewQuotaKVServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewKVServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newBackendQuota
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID

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

theorem v3rpc.NewQuotaKVServer.wp_proof
    (wp_NewKVServer : v3rpc.NewKVServer.spec (GF := GF) (hG := hG))
    (wp_newBackendQuota : v3rpc.newBackendQuota.spec (GF := GF) (hG := hG))
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG)) :
    v3rpc.NewQuotaKVServer.spec (GF := GF) (hG := hG) := by
  intro s A n lg qb mid
  wp_start as ⟨#HKV, #Hn, #Hlg, %Hlgn, Hlr, #Hqb, Hbr, #Hmid⟩
  wp_auto
  wp_apply wp_NewKVServer s A n $$ [] as %kv ⟨%p, %cid, %mid', %Hkv, #Hp⟩
  · iframe #
  subst Hkv
  wp_apply wp_newBackendQuota s lg qb go!"kv" $$ [Hlr Hbr] as %qv ⟨#Hq, Hlr, Hbr⟩
  · iframe; iframe #; ipureintro; exact Hlgn
  wp_apply wp_MemberID s mid $$ []
  · iframe #
  wp_alloc q as Hqv
  ihave %Hqn := typedPointsto_not_null _ _ _ $$ Hqv
  iStructNamed Hqv
  iStructNamed qa
  ipersist KVServer
  ipersist q
  ipersist a
  ipersist id
  wp_auto
  iapply HΦ
  iexists q, p, cid, mid'
  isplitr
  · ipureintro; rfl
  iframe
  iframe #
  iunfold v3rpc.quotaKVServerAt
  iframe #
  isplitr
  · ipureintro; exact Hqn
  iunfold v3rpc.quotaAlarmerAt
  iexists qv, mid
  iframe #

end proof

end EtcdGrove
end Perennial
