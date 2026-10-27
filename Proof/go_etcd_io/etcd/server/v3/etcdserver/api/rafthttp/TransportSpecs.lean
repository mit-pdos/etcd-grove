/-
**The transport's specs, proved over their callees'** (rafthttp stage 6d, 2026-10-24): `Start`,
`AddPeer`, `AddRemote`, `CutPeer`, `MendPeer` and `Handler`: their `wp_proof`s (axioms until
stage 6f, which linked rafthttp's functions) are these theorems. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportFull
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__AddPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__AddRemote
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__CutPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__MendPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Handler

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option maxRecDepth 8000 in
theorem rafthttp.Transport.Start_ok
    (hNSRT : rafthttp.newStreamRoundTripper.spec (GF := GF) (hG := hG))
    (hNRT : rafthttp.NewRoundTripper.spec (GF := GF) (hG := hG))
    (hNewProber : probing.NewProber.spec (GF := GF) (hG := hG))
    (hEvery : rate.Every.spec (GF := GF) (hG := hG))
    (hSend : rafthttp.Transport.Send.spec (GF := GF) (hG := hG))
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (hSS : rafthttp.Transport.SendSnapshot.spec (GF := GF) (hG := hG))
    (hAS : rafthttp.Transport.ActiveSince.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.Start.spec (GF := GF) (hG := hG) := by
  intro γn t tv R γd Rm uvs L
  wp_start_folded as ⟨Ht, %Hpre, #Huvs, #Hraft, #Hss, #Hdir, #Hnet, #Hlsi, Hlsf, HRL⟩
  wp_apply (rafthttp.Transport.Start_full hNSRT hNRT hNewProber hEvery γn t tv R γd Rm uvs L)
    $$ [Ht Hlsf HRL] as %err Hres
  · iframe; iframe #; ipureintro; exact Hpre
  iapply HΦ
  icases Hres with (%He | ⟨%He, %c, %Hc, Hl, Htoks⟩)
  · ileft; ipureintro; exact He
  iright
  isplitr
  · ipureintro; exact He
  iexists c
  ihave #Hst : trState γn t c $$ [Hl]
  · iunfold trLive at Hl; icases Hl with ⟨#Hst, -⟩; iexact Hst
  ihave ⟨#Hnet, #Htr⟩ := trState_net hSend hPeerStop hRemoteStop hSS hAS γn t c $$ [Hpkg Hst]
  · iframe #
  iframe
  isplitr
  · ipureintro; exact Hc
  iframe #
  imodintro
  iintro %rs #Hf
  ihave ⟨#Hn, -⟩ := trFrozen_net hSend hPeerStop hRemoteStop hSS hAS γn t c rs $$ [Hpkg Hf]
  · iframe #
  iexact Hn

theorem rafthttp.Transport.AddPeer_ok
    (hNewURLs : types.NewURLs.spec (GF := GF) (hG := hG))
    (hFollower : v2stats.LeaderStats.Follower.spec (GF := GF) (hG := hG))
    (hStartPeer : rafthttp.startPeer.spec (GF := GF) (hG := hG))
    (hProber : rafthttp.addPeerToProber.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZStrings : zap.Strings.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.AddPeer.spec (GF := GF) (hG := hG) :=
  fun γn t c rs id us dq ss Hne Hpl Hown Hself Hpm =>
    rafthttp.Transport.AddPeer_full hNewURLs hFollower hStartPeer hProber hIDString hIDStringPtr
      hInfo hZString hZStrings γn t c rs id us dq ss Hne Hpl Hown Hself Hpm

theorem rafthttp.Transport.AddRemote_ok
    (hNewURLs : types.NewURLs.spec (GF := GF) (hG := hG))
    (hStartRemote : rafthttp.startRemote.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZStrings : zap.Strings.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.AddRemote.spec (GF := GF) (hG := hG) :=
  fun γn t c id us dq ss Hne Hpl Hown Hself Hpm HL =>
    rafthttp.Transport.AddRemote_full hNewURLs hStartRemote hIDStringPtr hInfo hZString hZStrings
      γn t c id us dq ss Hne Hpl Hown Hself Hpm HL

theorem rafthttp.Transport.CutPeer_ok
    (hM : rafthttp.peer.Pause.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.CutPeer.spec (GF := GF) (hG := hG) := by
  intro hpp γn t c id Hid
  haveI := hpp
  exact rafthttp.Transport.CutPeer_full hM γn t c id Hid

theorem rafthttp.Transport.MendPeer_ok
    (hM : rafthttp.peer.Resume.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.MendPeer.spec (GF := GF) (hG := hG) := by
  intro hpp γn t c id Hid
  haveI := hpp
  exact rafthttp.Transport.MendPeer_full hM γn t c id Hid

theorem rafthttp.Transport.Handler_ok
    (hNPH : rafthttp.newPipelineHandler.spec (GF := GF) (hG := hG))
    (hNSH : rafthttp.newStreamHandler.spec (GF := GF) (hG := hG))
    (hNSnH : rafthttp.newSnapshotHandler.spec (GF := GF) (hG := hG))
    (hNewHandler : probing.NewHandler.spec (GF := GF) (hG := hG))
    (hGet : rafthttp.Transport.Get.spec (GF := GF) (hG := hG))
    (hPServe : rafthttp.pipelineHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (hSServe : rafthttp.streamHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (hSnServe : rafthttp.snapshotHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (hARR : rafthttp.addRemoteFromRequest.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.Handler.spec (GF := GF) (hG := hG) :=
  fun γn t c rs a Hown Hcov =>
    rafthttp.Transport.Handler_full hNPH hNSH hNSnH hNewHandler hGet hPServe hSServe hSnServe hARR γn t c rs
      a Hown Hcov

end proof

end EtcdGrove
end Perennial
