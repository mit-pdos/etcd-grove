/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewQuotaLeaseServer.lean` (item 4, the server
start). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewQuotaLeaseServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewLeaseServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newBackendQuota
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.NewQuotaLeaseServer.wp_proof
    (wp_NewLeaseServer : v3rpc.NewLeaseServer.spec (GF := GF) (hG := hG))
    (wp_newBackendQuota : v3rpc.newBackendQuota.spec (GF := GF) (hG := hG))
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG)) :
    v3rpc.NewQuotaLeaseServer.spec (GF := GF) (hG := hG) := by
  intro s A lg0 lg qb mid Hbuq
  wp_start as ⟨#HKV, #Hlg0, #Hlg, %Hlgn, Hlr, #Hqb, Hbr, #Hmid⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_NewLeaseServer s A lg0 $$ [] as %ls ⟨%p, %Hls⟩
  · iframe #
  subst Hls
  wp_apply wp_newBackendQuota s lg qb go!"lease" Hbuq $$ [Hlr Hbr] as %qv ⟨#Hq, Hlr, Hbr⟩
  · iframe; iframe #; ipureintro; exact Hlgn
  wp_apply wp_MemberID s mid $$ []
  · iframe #
  wp_alloc q as Hqv
  wp_auto
  iapply HΦ
  iframe
  iexists q
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
