/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer__MemberList
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer__header
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.membersToProtoMembers
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberList
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.TogRPCErrorPlain


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

theorem v3rpc.ClusterServer.MemberList.wp_proof
    (hML : EtcdServer.MemberList.spec (GF := GF) (hG := hG))
    (hHdr : v3rpc.ClusterServer.header.spec (GF := GF) (hG := hG))
    (hM2P : v3rpc.membersToProtoMembers.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG)) :
    v3rpc.ClusterServer.MemberList.spec (GF := GF) (hG := hG) := by
  intro p s cl E ρ γr ctx cd tok r lin dq c g Q n
  wp_start as ⟨#Hcs, #Hh, #Hq, #Hrd, #Hlb, #Hctx, #Hlib, #HtokC, HRD, Hr, Hrr, #Hc, #Hg, #Hdep⟩
  ihave #Hcs' := Hcs
  iunfold v3rpc.clusterServerIs at Hcs'
  icases Hcs' with ⟨#Hcl, #Hsv⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  wp_auto
  wp_apply (hML s E ρ γr ctx cd tok r lin dq c g Q n) $$ [$HRD $Hr $Hrr]
    as %sl %err ⟨HRD, Hr, Hrr, #Hae, Hwhy, Hok⟩
  · iframe #
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    wp_apply (v3rpc.togRPCError_out hTog) $$ [] as %e ⟨%He, #Hse, #Hgo⟩
    · iframe #
      iapply (v3rpc.srvErrIs_applyErrIs (GoInterface.ok ei) (by intro h; cases h)) $$ Hae
    (try wp_auto)
    iapply HΦ
    iframe HRD Hr Hrr Hse
    isplitl [Hwhy]
    · iintro %_
      isplitr
      · ipureintro; rfl
      iexists GoInterface.ok ei
      isplitr
      · ipureintro; nofun
      iframe Hgo
      ispecialize Hwhy $$ %(by nofun)
      iexact Hwhy
    · iintro %h; exact absurd h He
  · (try wp_auto)
    ispecialize Hok $$ %rfl
    icases Hok with ⟨⟨%ms, Hms⟩, #Hai, Hlin⟩
    wp_apply (hM2P sl ms) $$ [Hms] as %psl -
    · iframe
    (try wp_auto)
    wp_apply (hHdr p s cl) $$ [] as %h -
    · iframe #
    (try wp_auto)
    iapply HΦ
    iframe HRD Hr Hrr
    isplitr
    · iapply go_etcd_io.etcd.cache.v3.srvErrOk_nil
    isplitr
    · iintro %h; exact absurd rfl h
    iintro %_
    iframe Hai Hlin

end proof

end EtcdGrove
end Perennial
