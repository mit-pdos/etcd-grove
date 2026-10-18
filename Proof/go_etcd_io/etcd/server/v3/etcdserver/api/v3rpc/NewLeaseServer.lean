/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewLeaseServer.lean` (item 4, the server
start). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewLeaseServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newHeader
public import Spec.go_uber_org.zap.NewNop

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

theorem v3rpc.NewLeaseServer.wp_proof
    (hHdr : v3rpc.newHeader.spec (GF := GF) (hG := hG))
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG)) :
    v3rpc.NewLeaseServer.spec (GF := GF) (hG := hG) := by
  intro s A lg0
  wp_start as ⟨#HKV, #Hlg0⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  wp_apply (hHdr s A) as %hv ⟨%cid, %mid, #Hhv⟩
  · iframe #
  ihave %Hpn := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamed «$r0»
  iStructNamed hdr
  ipersist clusterID
  ipersist memberID
  ipersist sg
  ipersist rev
  ipersist le
  iunfold v3rpc.hdrValIs at Hhv
  icases Hhv with ⟨%Hhv, #HrevS, #Hrs⟩
  obtain ⟨Hc, Hm, Hsg⟩ := Hhv
  ihave #Hat : v3rpc.leaseServerAt «$r0_ptr» s A cid mid $$ []
  · iunfold v3rpc.leaseServerAt
    iunfold v3rpc.hdrIs
    iframe #
    rw [Hc, Hm, Hsg]
    iframe #
    ipureintro; exact Hpn
  wp_if_destruct
  · wp_apply hNop as %l -
    (try wp_auto)
    iapply HΦ
    iexists «$r0_ptr», cid, mid
    iframe #
    ipureintro; rfl
  · (try wp_auto)
    iapply HΦ
    iexists «$r0_ptr», cid, mid
    iframe #
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
