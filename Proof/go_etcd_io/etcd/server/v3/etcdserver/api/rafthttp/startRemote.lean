/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/startRemote.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.startRemote
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newPeerStatus
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newURLPicker
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline__start

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option maxHeartbeats 4000000 in
theorem rafthttp.startRemote.wp_proof
    (hNewStatus : rafthttp.newPeerStatus.spec (GF := GF) (hG := hG))
    (hNewPicker : rafthttp.newURLPicker.spec (GF := GF) (hG := hG))
    (hPipeStart : rafthttp.pipeline.start.spec (GF := GF) (hG := hG)) :
    rafthttp.startRemote.spec (GF := GF) (hG := hG) := by
  intro Rh t lid γd R urls uvs pid Hne Hurls Hmem Hnp Hpm
  wp_start as ⟨#Htr, #Hus, HR1, HR2, HR3, HR4⟩
  ihave #Htr' := Htr
  iunfold trFixed at Htr'
  icases Htr' with ⟨%lg, %ls, %ss, %turls, %tuvs, %cid, %r, %ec, %srt, %prt, %drf, %ppr, %spr, #Hlg, %Hlgnn,
    #Hlid, #HtURLs, #Htuvs, #Hcid, #Hr, #Hraft, #Hec, #Hsrt, #Hsrtok, #Hprt, #Hprtok, #Hdrf, #Hls,
    %Hlsnn, #Hss, %Hssnn, #Hppr, #Hspr, #Hreg, #Hpreg0, #HPfx, %HmemU⟩
  obtain ⟨Hmem, Hturls⟩ := HmemU
  have Hpp : Rh.member pid ∧ pid ≠ lid := ⟨Hpm, fun h => Hnp h.symm⟩
  ihave #Hpreg := Hpreg0 $$ %pid %Hpp
  wp_auto
  wp_apply hNewPicker urls uvs (peerURL Rh pid) Hne Hurls $$ [] as %pk #Hpk
  · iframe #
  (try wp_auto)
  wp_apply hNewStatus lg lid pid Hlgnn as %ps #Hps
  (try wp_auto)
  iStructNamedSuffix «$r0» "P"
  ipersist peerIDP; ipersist trP; ipersist pickerP; ipersist statusP; ipersist raftP
  ipersist errorcP; ipersist followerStatsP
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") («$r0_ptr».[rafthttp.pipeline, go!"wg"]) $$ wgP
    with ⟨%γwg, Hwg⟩
  imod sync.join.init _ γwg $$ Hwg with Hwg
  wp_apply hPipeStart Rh «$r0_ptr» pid R $$ [msgcP stopcP Hwg HR1 HR2 HR3 HR4] as Hpl
  · iframe
    iunfold pipeFixed
    iexists t, pk, ec, lg, turls, tuvs, lid, cid, prt, ps, null, r, lid, γd
    iframe #
    isplitr
    · ipureintro; exact Hlgnn
    isplitr
    · ipureintro; exact ⟨Hmem, Hnp⟩
    ipureintro; exact Hturls
  (try wp_auto)
  obtain ⟨pl, hpl⟩ : ∃ pl : Loc, pl = «$r0_ptr» := ⟨_, rfl⟩
  subst hpl
  ihave #Hph : pipeHandleOk Rh pl pid R $$ [Hpl]
  · iunfold pipeStarted at Hpl
    icases Hpl with ⟨#Hph, -⟩
    iexact Hph
  wp_alloc g as Hg
  iStructNamed Hg
  ipersist lg; ipersist localID; ipersist id; ipersist status; ipersist pipeline
  (try wp_auto)
  iapply HΦ
  isplitr
  · iunfold remoteOk
    iexists lg, ps, pl
    iframe #
    ipureintro; exact Hlgnn
  iunfold remoteStop
  iexists pl
  iframe; iframe #

end proof

end EtcdGrove
end Perennial
