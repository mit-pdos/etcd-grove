/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewQuotaLeaseServer.lean` (item 4, the server
start). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewQuotaLeaseServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewLeaseServer

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
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

theorem v3rpc.NewQuotaLeaseServer.wp_proof
    (wp_NewLeaseServer : v3rpc.NewLeaseServer.spec (GF := GF) (hG := hG)) :
    v3rpc.NewQuotaLeaseServer.spec (GF := GF) (hG := hG) := by
  intro s A lg0 lg qb Hbuq
  wp_start as ⟨#HKV, #Hlg0, #Hlg, %Hlgn, #Hqb⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_NewLeaseServer s A lg0 $$ [] as %ls ⟨%p, %cid, %mid', %Hls, #Hp⟩
  · iframe #
  subst Hls
  wp_alloc q as Hqv
  ihave %Hqn := typedPointsto_not_null _ _ _ $$ Hqv
  iStructNamed Hqv
  iStructNamed qa
  ipersist LeaseServer
  ipersist s
  ipersist name
  wp_auto
  iapply HΦ
  iexists q, p, cid, mid'
  isplitr
  · ipureintro; rfl
  iframe
  iframe #
  iunfold v3rpc.quotaLeaseServerAt
  iframe #
  isplitr
  · ipureintro; exact Hqn
  iunfold v3rpc.quotaAlarmerAt
  iexists go!"lease", lg, qb
  iframe #
  ipureintro; exact ⟨Hlgn, Hbuq⟩

end proof

end EtcdGrove
end Perennial
