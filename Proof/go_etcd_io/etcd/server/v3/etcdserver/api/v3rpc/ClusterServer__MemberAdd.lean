/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer__MemberAdd
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer__header
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.membersToProtoMembers
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AddMember
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.NewURLs
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

set_option hygiene false in
/-- After the member `m ↦ memb` is made (`Hlrn` its learner flag): `AddMember`, then `togRPCError`
or the response. -/
local macro "add_rest" : tactic => `(tactic| (
  wp_apply (hAM s E ctx cd tok memb (DFrac.own 1) (DFrac.own 1) mps [] Pin Pm (memChkAns Qm)
      (memCfgAns Qin) n) $$ [HRD HPin HPm Hsls] as %sl %err ⟨HRD, Hsls, Hout⟩
  · iframe #
    iframe
    isplitl []
    · iapply Hmay
    rw [Hlrn]
    iapply Hconf
  (try wp_auto)
  icases Hout with (HQ | ⟨%Hne, HPin, (⟨#Hae, #Hw, HPm⟩ | HQm)⟩)
  · iunfold memCfgAns at HQ
    icases HQ with ⟨HQ, (⟨%Hen, %ms, Hms⟩ | ⟨%Hen, #Hae, -⟩)⟩
    · subst Hen
      (try wp_auto)
      iStructNamed Hm
      iStructNamed RaftAttributes
      (try wp_auto)
      wp_apply (hHdr p s cl) $$ [] as %h -
      · iframe #
      (try wp_auto)
      wp_apply (hM2P sl ms) $$ [Hms] as %psl' -
      · iframe
      (try wp_auto)
      iapply HΦ
      iframe HRD Hrp Hps Hrl
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
        iframe HRD Hrp Hps Hrl
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
      iframe HRD Hrp Hps Hrl
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
      iframe HPin
      ileft
      iframe Hw HPm
    · exact absurd rfl Hne
  · iunfold memChkAns at HQm
    icases HQm with ⟨HQm, (%Hen | ⟨#Hae, -⟩)⟩
    · exact absurd Hen Hne
    rcases err with ei | _
    · (try wp_auto)
      wp_apply (v3rpc.togRPCError_out hTog) $$ [] as %e ⟨%He, #Hse, #Hgo⟩
      · iframe #
        iapply (v3rpc.srvErrIs_applyErrIs (GoInterface.ok ei) (by intro h; cases h)) $$ Hae
      (try wp_auto)
      iapply HΦ
      iframe HRD Hrp Hps Hrl
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
      iframe HPin
      iright
      iexact HQm
    · exact absurd rfl Hne))

theorem v3rpc.ClusterServer.MemberAdd.wp_proof
    (hAM : EtcdServer.AddMember.spec (GF := GF) (hG := hG))
    (hURLs : types.NewURLs.spec (GF := GF) (hG := hG))
    (hHdr : v3rpc.ClusterServer.header.spec (GF := GF) (hG := hG))
    (hM2P : v3rpc.membersToProtoMembers.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG)) :
    v3rpc.ClusterServer.MemberAdd.spec (GF := GF) (hG := hG) := by
  intro p s cl E ctx cd tok r dq psl ps lrn Pin Pm Qm Qin n Hne Hplain
  wp_start as ⟨#Hcs, #Hh, #Hau, #Hlb, #Hctx, #Hlib, #HtokC, HRD, HPin, HPm, Hrp, Hps, Hrl, #Hnm,
    #Hmay, #Hconf⟩
  ihave #Hcs' := Hcs
  iunfold v3rpc.clusterServerIs at Hcs'
  icases Hcs' with ⟨#Hcl, #Hsv⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  wp_auto
  wp_apply (hURLs psl dq ps Hne Hplain) $$ [Hps] as %us %uvs ⟨Hps, Hus, %Huvs⟩
  · iframe #; iframe Hps
  (try wp_auto)
  wp_apply time.wp_Now as %tv -
  (try wp_auto)
  iunfold v3rpc.newMemberOk at Hnm
  icases Hnm with ⟨#HnL, #HnM⟩
  cases lrn
  · (try wp_auto)
    wp_apply HnM $$ %us %uvs %now_ptr %tv [Hus now] as %m ⟨Hus, now, %memb, %mps, Hm, Hsls, %Hlrn⟩
    · iframe
    (try wp_auto)
    add_rest
  · (try wp_auto)
    wp_apply HnL $$ %us %uvs %now_ptr %tv [Hus now] as %m ⟨Hus, now, %memb, %mps, Hm, Hsls, %Hlrn⟩
    · iframe
    (try wp_auto)
    add_rest

end proof

end EtcdGrove
end Perennial
