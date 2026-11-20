/-
Proof of the spec of the same name (the client lease's stage (c)). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.TogRPCErrorPlain
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fill

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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.LeaseServer.LeaseRevoke.wp_proof
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (hFill : v3rpc.header.fill.spec (GF := GF) (hG := hG)) :
    v3rpc.LeaseServer.LeaseRevoke.spec (GF := GF) (hG := hG) := by
  intro p s A cid mid on E ρ S ci tok cd r m Q n
  wp_start as ⟨#Hls, #HR, HS, #Hn, #Hctx, #Hrc, #Htk, #Hr, Hp⟩
  ihave #Hls' := Hls
  iunfold v3rpc.leaseServerAt at Hls'
  icases Hls' with ⟨%Hpn, #Hhdr, #Hle, -⟩
  iunfold v3rpc.lessorRevokeOkM at HR
  wp_auto
  wp_apply HR $$ %ci %tok %cd %r %m %Q %n [HS Hp] as %resp %err ⟨HS, Hans, Hres⟩
  · iframe; iframe #
  iunfold v3rpc.leaseRevokeAns at Hans
  icases Hans with (⟨%Hok, Hh⟩ | #Hse)
  · obtain ⟨He, Hrn⟩ := Hok
    subst He
    iunfold v3rpc.leaseHdrAns at Hh
    icases Hh with ⟨%h, %rv, #Hhf, Hw, %Hr0, #Hrev, #Hreach⟩
    ihave Hin : v3rpc.hdrRevIn A.revR h rv $$ []
    · iunfold v3rpc.hdrRevIn
      ileft
      iframe #
      ipureintro; exact Hr0
    wp_auto
    wp_apply hFill $$ [Hw Hin] as ⟨Hfd, %rv', -⟩
    · iframe; iframe #
    wp_auto
    ihave #HSn := go_etcd_io.etcd.cache.v3.srvErrOk_nil (GF := GF)
    iapply HΦ
    iframe HSn
    iframe HS Hres
    iunfold v3rpc.leaseRevokeOut
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, Hrn⟩
    iunfold v3rpc.leaseHdrOut
    iexists h, rv
    iframe
    iframe #
    ipureintro; exact Hr0
  · ihave #Hse' := Hse
    iunfold v3rpc.srvErrIs at Hse'
    icases Hse' with ⟨%Hen, -⟩
    cases err with
    | nil => exact absurd rfl Hen
    | ok ei =>
      wp_auto
      wp_apply (v3rpc.togRPCError_plain hTog) $$ [] as %e ⟨%He, #HSn⟩
      · iframe #
      iapply HΦ
      iframe HSn
      iframe HS
      isplitl []
      · iunfold v3rpc.leaseRevokeOut
        iright
        ipureintro; exact ⟨rfl, He⟩
      ileft; ipureintro; exact He

end proof

end EtcdGrove
end Perennial
