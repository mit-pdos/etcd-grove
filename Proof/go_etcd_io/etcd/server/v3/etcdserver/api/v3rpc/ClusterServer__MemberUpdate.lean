/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer__MemberUpdate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer__header
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.membersToProtoMembers
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__UpdateMember
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

theorem v3rpc.ClusterServer.MemberUpdate.wp_proof
    (hUM : EtcdServer.UpdateMember.spec (GF := GF) (hG := hG))
    (hHdr : v3rpc.ClusterServer.header.spec (GF := GF) (hG := hG))
    (hM2P : v3rpc.membersToProtoMembers.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG)) :
    v3rpc.ClusterServer.MemberUpdate.spec (GF := GF) (hG := hG) := by
  intro p s cl E ctx cd tok r dq id psl dp ps Pin Qin n
  wp_start as ⟨#Hcs, #Hh, #Hau, #Hlb, #Hctx, #Hlib, #HtokC, HRD, HPin, Hrid, Hrpu, Hps, #Hconf⟩
  ihave #Hcs' := Hcs
  iunfold v3rpc.clusterServerIs at Hcs'
  icases Hcs' with ⟨#Hcl, #Hsv⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave Hn := ownSlice_nil (V := GoString) (GF := GF) (DFrac.own 1)
  wp_auto
  wp_apply (hUM s E ctx cd tok _ dp (DFrac.own 1) ps [] Pin (memCfgAns Qin) n)
    $$ [$HRD $HPin Hps Hn] as %sl %err ⟨HRD, Hsls, Hout⟩
  · iframe #
    iunfold memberSlices
    iframe
    iexact Hn
  (try wp_auto)
  iunfold memberSlices at Hsls
  icases Hsls with ⟨Hps, -⟩
  icases Hout with (HQ | ⟨%Hne, HPin, #Hae, #Hw⟩)
  · iunfold memCfgAns at HQ
    icases HQ with ⟨HQ, (⟨%Hen, %ms, Hms⟩ | ⟨%Hen, #Hae, -⟩)⟩
    · subst Hen
      (try wp_auto)
      wp_apply (hHdr p s cl) $$ [] as %h -
      · iframe #
      (try wp_auto)
      wp_apply (hM2P sl ms) $$ [Hms] as %psl' -
      · iframe
      (try wp_auto)
      iapply HΦ
      iframe HRD Hrid Hrpu Hps
      iunfold v3rpc.memberOutC
      isplitr
      · iapply go_etcd_io.etcd.cache.v3.srvErrOk_nil
      ileft
      isplitr
      · ipureintro; rfl
      iexists sl
      iexact HQ
    · rcases err with ei | _
      · (try wp_auto)
        wp_apply (v3rpc.togRPCError_out hTog) $$ [] as %e ⟨%He, #Hse, #Hgo⟩
        · iframe #
          iapply (v3rpc.srvErrIs_applyErrIs (GoInterface.ok ei) (by intro h; cases h)) $$ Hae
        (try wp_auto)
        iapply HΦ
        iframe HRD Hrid Hrpu Hps
        iunfold v3rpc.memberOutC
        iframe Hse
        iright
        isplitr
        · ipureintro; exact ⟨rfl, He⟩
        iexists GoInterface.ok ei
        isplitr
        · ipureintro; nofun
        iframe Hgo
        ileft
        iexists sl
        iexact HQ
      · exact absurd rfl Hen
  · rcases err with ei | _
    · (try wp_auto)
      wp_apply (v3rpc.togRPCError_out hTog) $$ [] as %e ⟨%He, #Hse, #Hgo⟩
      · iframe #
        iapply (v3rpc.srvErrIs_applyErrIs (GoInterface.ok ei) (by intro h; cases h)) $$ Hae
      (try wp_auto)
      iapply HΦ
      iframe HRD Hrid Hrpu Hps
      iunfold v3rpc.memberOutC
      iframe Hse
      iright
      isplitr
      · ipureintro; exact ⟨rfl, He⟩
      iexists GoInterface.ok ei
      isplitr
      · ipureintro; nofun
      iframe Hgo
      iright
      iframe HPin Hw
    · exact absurd rfl Hne

end proof

end EtcdGrove
end Perennial
