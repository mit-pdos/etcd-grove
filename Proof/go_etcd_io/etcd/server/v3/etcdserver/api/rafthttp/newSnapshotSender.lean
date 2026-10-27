/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/newSnapshotSender.lean` (rafthttp
stage 7d; an axiom from stage 6b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newSnapshotSender
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

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

theorem rafthttp.newSnapshotSender.wp_proof :
    rafthttp.newSnapshotSender.spec (GF := GF) (hG := hG) := by
  intro Rh t lid γd R pk pid ps Hpm Hne
  wp_start as ⟨#Htr, #Hpk, #Hps⟩
  ihave #Htr' := Htr
  iunfold trFixed at Htr'
  icases Htr' with ⟨%lg, %ls, %ss0, %turls, %tuvs, %cid, %r, %ec, %srt, %prt, %drf, %ppr, %spr,
    #Hlg, %Hlgnn, #Hlid, #HtURLs, #Htuvs, #Hcid, #Hr, #Hraft, #Hec, #Hsrt, #Hsrtok, #Hprt, #Hprtok,
    #Hdrf, #Hls, %Hlsnn, #Hss, %Hssnn, #Hppr, #Hspr, #Hreg, #Hpreg, #HPfx, %⟨Hmem, Hturls⟩⟩
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %sc %γs ⟨#Hscc, %-, Hsco⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γs sc $$ Hscc Hsco with Hbc
  (try wp_auto)
  wp_alloc s as Hs
  iStructNamed Hs
  ipersist from'; ipersist to; ipersist cid; ipersist tr; ipersist picker; ipersist status
  ipersist r; ipersist errorc; ipersist stopc
  icases ownBroadcastChan_open _ _ _ _ $$ Hbc with ⟨%γch, #Hint, Hown⟩
  ihave #Hunk : ownBroadcastChan sc γs iprop(True) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γch
    isplit
    · iexact Hint
    · itrivial
  ihave Hbc := ownBroadcastChan_close sc γs iprop(True) .Pending γch $$ [$Hint $Hown]
  (try wp_auto)
  iapply HΦ
  isplitr
  · iunfold snapSenderOk
    iexists t, pk, ps, r, ec, sc, γs, lg, turls, tuvs, lid, cid, prt, γd, R
    iframe #
    isplitr
    · ipureintro; exact Hlgnn
    isplitr
    · iapply Hpreg
      ipureintro; exact ⟨Hpm, Hne⟩
    isplitr
    · ipureintro; exact ⟨Hmem, fun h => Hne h.symm⟩
    ipureintro; exact Hturls
  iunfold snapSenderStop
  iexists sc, γs
  iframe #; iframe

end proof

end EtcdGrove
end Perennial
