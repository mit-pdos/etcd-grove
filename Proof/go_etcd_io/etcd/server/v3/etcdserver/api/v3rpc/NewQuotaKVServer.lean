/-
Proof of the spec of the same name (unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewQuotaKVServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewKVServer

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.NewQuotaKVServer.wp_proof
    (wp_NewKVServer : v3rpc.NewKVServer.spec (GF := GF) (hG := hG)) :
    v3rpc.NewQuotaKVServer.spec (GF := GF) (hG := hG) := by
  intro s A n lg qb Hbuq Hmx
  wp_start as ⟨#HKV, #Hn, #Hlg, %Hlgn, #Hqb⟩
  wp_auto
  wp_apply wp_NewKVServer s A n Hmx $$ [] as %kv ⟨%p, %cid, %mid', %Hkv, #Hp⟩
  · iframe #
  subst Hkv
  wp_alloc q as Hqv
  ihave %Hqn := typedPointsto_not_null _ _ _ $$ Hqv
  iStructNamed Hqv
  iStructNamed qa
  ipersist KVServer
  ipersist s
  ipersist name
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
  iexists go!"kv", lg, qb
  iframe #
  ipureintro; exact ⟨Hlgn, Hbuq⟩

end proof

end EtcdGrove
end Perennial
