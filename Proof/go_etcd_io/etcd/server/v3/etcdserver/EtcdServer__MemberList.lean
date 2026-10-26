/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__MemberList.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberList
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__requireAuthInfo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.MemberList.wp_proof
    (hReq : EtcdServer.requireAuthInfo.spec (GF := GF) (hG := hG))
    (hMem : membership.RaftCluster.Members.spec (GF := GF) (hG := hG)) :
    EtcdServer.MemberList.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr ctx cd r lin dq c g Q
  wp_start as ⟨#Hq, #Hr, #Hctx, HRD, Hlin, Hrr, #Hc, #HsQ, #HdQ⟩
  ihave #Hau : srvAuthAt s E $$ []
  · iapply (srvAuthAt_of_views s E ρ γr); iframe #
  ihave #Hr' := Hr
  iunfold isServerRead at Hr'
  icases Hr' with ⟨%vr, Hr'⟩
  iunfold srvReadFieldsAt at Hr'
  icases Hr' with ⟨#Hrd, #HRN, -⟩
  ihave #Hq' := Hq
  iunfold isServerReq at Hq'
  icases Hq' with ⟨%vq, Hq'⟩
  iunfold srvReqFieldsAt at Hq'
  icases Hq' with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hcl, -, #Hpeers, -⟩
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨-, #Hrc, -⟩
  iunfold srvReadReader at Hrr
  icases Hrr with ⟨%rd, #Hrd2, Hrr⟩
  icombine Hrd Hrd2 gives %Heq
  subst Heq
  ihave #Hpmem : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  (try wp_auto)
  cases lin
  · (try wp_auto)
    wp_apply (hReq s E ctx cd) $$ [$HRD] as %err ⟨HRD, #Hout⟩
    · iframe #
    iunfold authedOut at Hout
    icases Hout with ⟨#Herr, -, #Htok, -⟩
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      iapply HΦ
      iframe HRD Hlin Herr
      isplitl [Hrr]
      · iunfold srvReadReader; iexists vr.read; iframe #; iframe Hrr
      iintro %h; cases h
    · (try wp_auto)
      wp_apply (membership.RaftCluster.Members.spec_static hMem vq.cluster) $$ [] as %sl ⟨%ms, Hms⟩
      · iframe #
      (try wp_auto)
      iapply HΦ
      iframe HRD Hlin Herr
      isplitl [Hrr]
      · iunfold srvReadReader; iexists vr.read; iframe #; iframe Hrr
      iintro %_
      isplitl [Hms]
      · iexists ms; iexact Hms
      ispecialize Htok $$ %rfl
      iframe #
      iintro %h; cases h
  · (try wp_auto)
    iunfold isReadNotify at HRN
    ispecialize HRN $$ %ctx %cd %c %g %Q
    wp_apply HRN $$ [$Hrr] as %err Herr
    · iframe #
    icases Herr with ⟨Hrr, #Herr, Hri⟩
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      iapply HΦ
      iframe HRD Hlin Herr
      isplitl [Hrr]
      · iunfold srvReadReader; iexists vr.read; iframe #; iframe Hrr
      iintro %h; cases h
    · (try wp_auto)
      ihave Hri' : (readIndexOk γr c ∗ readServed γr c g) $$ [Hri]
      · iapply Hri; ipureintro; rfl
      wp_apply (hReq s E ctx cd) $$ [$HRD] as %err2 ⟨HRD, #Hout⟩
      · iframe #
      iunfold authedOut at Hout
      icases Hout with ⟨#Herr2, -, #Htok, -⟩
      (try wp_auto)
      rcases err2 with ei | _
      · (try wp_auto)
        iapply HΦ
        iframe HRD Hlin Herr2
        isplitl [Hrr]
        · iunfold srvReadReader; iexists vr.read; iframe #; iframe Hrr
        iintro %h; cases h
      · (try wp_auto)
        wp_apply (membership.RaftCluster.Members.spec_static hMem vq.cluster) $$ [] as %sl ⟨%ms, Hms⟩
        · iframe #
        (try wp_auto)
        iapply HΦ
        iframe HRD Hlin Herr2
        isplitl [Hrr]
        · iunfold srvReadReader; iexists vr.read; iframe #; iframe Hrr
        iintro %_
        isplitl [Hms]
        · iexists ms; iexact Hms
        ispecialize Htok $$ %rfl
        iframe #
        iintro %_
        iexact Hri'

end proof

end EtcdGrove
end Perennial
