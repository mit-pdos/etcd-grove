/-
**The transport's methods over its state** (rafthttp stage 6d): `AddPeer`, `AddRemote` on a live
transport (`trLive`); `Send`, `CutPeer`, `MendPeer`, `Stop`, `Handler` on a frozen one
(`trFrozen`), the read-locked ones with a reader's token (`trTok`); a frozen transport as the
network's (`trFrozen_net`: `netTransport`, `isTransporter`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportState
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportAdd
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportCut
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportStop
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportHandler
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Send
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__SendSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__ActiveSince

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- `trState`'s parts, persistent: `Hfix`, `Hprb`, `Hstp`, `Hgd`, the snapshotter's `Hssf`,
`Hss`, `Hdir`. -/
local macro "tr_state" H:ident : tactic => `(tactic| (
  iunfold trState at $H:ident
  icases $H:ident with ⟨#Hfix, #Hprb, #Hstp, #Hgd, %sst, %Rm, #Hssf, #Hss, #Hdir⟩))

/-- **`t.AddPeer(id, us)`** on a live transport, of `id`'s URL strings (non-empty, plain, owned by
`id`), another member than its own, with eight `R`s: `id` among the peers' ids. -/
theorem rafthttp.Transport.AddPeer_full
    (hNewURLs : types.NewURLs.spec (GF := GF) (hG := hG))
    (hFollower : v2stats.LeaderStats.Follower.spec (GF := GF) (hG := hG))
    (hStartPeer : rafthttp.startPeer.spec (GF := GF) (hG := hG))
    (hProber : rafthttp.addPeerToProber.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZStrings : zap.Strings.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (id : w64) (us : GoSlice) (dq : DFrac)
    (ss : List GoString) (Hne : ss ≠ []) (Hpl : ∀ s ∈ ss, types.plainPeerURL s)
    (Hown : ∀ h, go!"http://" ++ h ∈ ss → (netRh γn).owner h = id) (Hself : c.lid ≠ id)
    (Hpm : (netRh γn).member id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trLive γn t c rs ∗ us ↦*{dq} ss ∗ [∗list] _x ∈ List.replicate 8 (), c.R }}
      (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddPeer")) (Val #id))
        (Val #us))
    {{ RET #(); trLive γn t c (rs.1, rs.2 ++ [id]) ∗ us ↦*{dq} ss }} := by
  wp_start_folded as ⟨Hl, Hus, HRs⟩
  iunfold trLive at Hl
  icases Hl with ⟨#Hst, Hg⟩
  ihave #Hst' := Hst
  tr_state Hst'
  wp_apply (rafthttp.Transport.AddPeer_core hNewURLs hFollower hStartPeer hProber hIDString
      hIDStringPtr hInfo hZString hZStrings (netRh γn) t c.lid c.γd c.R c.γs c.γr rs id us dq ss
      Hne Hpl Hown Hself Hpm) $$ [Hg Hus HRs] as ⟨Hg, Hus⟩
  · iframe; iframe #
  iapply HΦ
  iframe
  iunfold trLive
  iframe #
  iexact Hg

/-- **`t.AddRemote(id, us)`** on a live transport, as `AddPeer`, with four `R`s: `id` among the
remotes' ids. -/
theorem rafthttp.Transport.AddRemote_full
    (hNewURLs : types.NewURLs.spec (GF := GF) (hG := hG))
    (hStartRemote : rafthttp.startRemote.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZStrings : zap.Strings.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (id : w64) (us : GoSlice) (dq : DFrac)
    (ss : List GoString) (Hne : ss ≠ []) (Hpl : ∀ s ∈ ss, types.plainPeerURL s)
    (Hown : ∀ h, go!"http://" ++ h ∈ ss → (netRh γn).owner h = id) (Hself : c.lid ≠ id)
    (Hpm : (netRh γn).member id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trLive γn t c rs ∗ us ↦*{dq} ss ∗ c.R ∗ c.R ∗ c.R ∗ c.R }}
      (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddRemote"))
        (Val #id)) (Val #us))
    {{ RET #(); trLive γn t c (rs.1 ++ [id], rs.2) ∗ us ↦*{dq} ss }} := by
  wp_start_folded as ⟨Hl, Hus, HR1, HR2, HR3, HR4⟩
  iunfold trLive at Hl
  icases Hl with ⟨#Hst, Hg⟩
  ihave #Hst' := Hst
  tr_state Hst'
  wp_apply (rafthttp.Transport.AddRemote_core hNewURLs hStartRemote hIDStringPtr hInfo hZString
      hZStrings (netRh γn) t c.lid c.γd c.R c.γs c.γr rs id us dq ss Hne Hpl Hown Hself Hpm)
    $$ [Hg Hus HR1 HR2 HR3 HR4] as ⟨Hg, Hus⟩
  · iframe; iframe #
  iapply HΦ
  iframe
  iunfold trLive
  iframe #
  iexact Hg

/-- **`t.CutPeer(id)`** on a frozen transport with a reader's token, `id` no remote. -/
theorem rafthttp.Transport.CutPeer_full [PeerPausable] (hM : rafthttp.peer.Pause.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (id : w64) (Hid : id ∉ rs.1) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFrozen γn t c rs ∗ trTok γn t c }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"CutPeer")) (Val #id))
    {{ RET #(); trTok γn t c }} := by
  wp_start_folded as ⟨#Hf, Htok⟩
  iunfold trFrozen at Hf
  icases Hf with ⟨-, #Hfr⟩
  iunfold trTok at Htok
  wp_apply (rafthttp.Transport.CutPeer_core hM (netRh γn) t c.lid c.γd c.R c.γs c.γr rs id Hid)
    $$ [Htok] as Htok
  · iframe; iframe #
  iapply HΦ
  iunfold trTok
  iexact Htok

/-- **`t.MendPeer(id)`**, as `CutPeer`. -/
theorem rafthttp.Transport.MendPeer_full [PeerPausable] (hM : rafthttp.peer.Resume.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (id : w64) (Hid : id ∉ rs.1) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFrozen γn t c rs ∗ trTok γn t c }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"MendPeer")) (Val #id))
    {{ RET #(); trTok γn t c }} := by
  wp_start_folded as ⟨#Hf, Htok⟩
  iunfold trFrozen at Hf
  icases Hf with ⟨-, #Hfr⟩
  iunfold trTok at Htok
  wp_apply (rafthttp.Transport.MendPeer_core hM (netRh γn) t c.lid c.γd c.R c.γs c.γr rs id Hid)
    $$ [Htok] as Htok
  · iframe; iframe #
  iapply HΦ
  iunfold trTok
  iexact Htok

/-- **`t.Stop()`** on a frozen transport: it returns. -/
theorem rafthttp.Transport.Stop_full
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFrozen γn t c rs }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Stop")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as #Hf
  iunfold trFrozen at Hf
  icases Hf with ⟨#Hst, #Hfr⟩
  tr_state Hst
  wp_apply (rafthttp.Transport.Stop_core hPeerStop hRemoteStop (netRh γn) t c.lid c.γd c.R c.γs
    c.γr rs) $$ []
  · iframe #
  iapply HΦ; itrivial

/-- **`t.Send(msgs)`** on a frozen transport with a reader's token, of messages the member sends
(`sendMsg`). -/
theorem rafthttp.Transport.Send_full (hSend : rafthttp.Transport.Send.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (sl : GoSlice) (msL : List Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFrozen γn t c rs ∗ trTok γn t c ∗ sl ↦* msL ∗
        [∗list] m ∈ msL, sendMsg (netRh γn) c.lid m }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Send")) (Val #sl))
    {{ RET #(); trTok γn t c }} := by
  wp_start_folded as ⟨#Hf, Htok, Hsl, Hms⟩
  iunfold trFrozen at Hf
  icases Hf with ⟨#Hst, -⟩
  tr_state Hst
  iunfold trTok at Htok
  wp_apply (hSend (netRh γn) t c.lid c.γd c.R c.γs c.γr sl msL) $$ [Htok Hsl Hms] as Htok
  · iframe; iframe #
  iapply HΦ
  iunfold trTok
  iexact Htok

/-- **`t.Handler()`** on a frozen transport whose recorded peers cover every other member (a
static cluster's, all added before the freeze), of the member owning `a`: a handler of `a` for the
raft protocol, lending each invocation an `R` and a reader's token. -/
theorem rafthttp.Transport.Handler_full
    (hNPH : rafthttp.newPipelineHandler.spec (GF := GF) (hG := hG))
    (hNSH : rafthttp.newStreamHandler.spec (GF := GF) (hG := hG))
    (hNSnH : rafthttp.newSnapshotHandler.spec (GF := GF) (hG := hG))
    (hNewHandler : probing.NewHandler.spec (GF := GF) (hG := hG))
    (hGet : rafthttp.Transport.Get.spec (GF := GF) (hG := hG))
    (hPServe : rafthttp.pipelineHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (hSServe : rafthttp.streamHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (hARR : rafthttp.addRemoteFromRequest.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (a : GoString)
    (Hown : (netRh γn).owner a = c.lid)
    (Hcov : ∀ f, (netRh γn).member f → f ≠ c.lid → f ∈ rs.2) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFrozen γn t c rs }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Handler")) (Val #()))
    {{ (h : GoInterface), RET #h;
        http.handlerOk (raftHttpNet (netRh γn)) a iprop(c.R ∗ trTok γn t c) h }} := by
  wp_start_folded as #Hf
  iunfold trFrozen at Hf
  icases Hf with ⟨#Hst, #Hfr⟩
  tr_state Hst
  ihave #HAR := trAddRemote_of_frozen (netRh γn) t c.lid c.γd c.R c.γs c.γr rs Hcov $$ Hpkg Hgd Hfr
  ihave #HARR := trAddRemoteReq_of hARR (netRh γn) t c.lid $$ Hpkg HAR
  wp_apply (rafthttp.Transport.Handler_core hNPH hNSH hNSnH hNewHandler hGet hPServe hSServe
      (netRh γn) t c.lid c.γd c.R c.γs c.γr a sst Rm Hown) $$ [] as %h Hh
  · iframe #
    rw [show (netRh γn).γn = γn from rfl]
    iexact Hdir
  iapply HΦ
  iunfold trTok
  iexact Hh

/-- **A frozen transport is the network's** (stage 6d): `netTransport` of its member, its `Send`
borrowing a reader's token (`Send_full`, each message's bundle with its encoding's bound,
`sendMsg_of_netBundle`), its `Stop` (`Stop_full`) and `SendSnapshot` (the snapshot stream's
axiom); and its `ActiveSince` (`isTransporter`). -/
theorem trFrozen_net (hSend : rafthttp.Transport.Send.spec (GF := GF) (hG := hG))
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (hSS : rafthttp.Transport.SendSnapshot.spec (GF := GF) (hG := hG))
    (hAS : rafthttp.Transport.ActiveSince.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFrozen γn t c rs ⊢
      netTransport γn c.lid (interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t)
          (trTok γn t c) ∗
        rafthttp.isTransporter (interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t) := by
  iintro ⟨#Hpkg, #Hf⟩
  isplitr
  · iunfold netTransport
    iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · imodintro
      iintro %sl %msL %Φ !> ⟨Hsl, Hms, Htok⟩ HΦ
      wp_apply (rafthttp.Transport.Send_full hSend γn t c rs sl msL) $$ [Hsl Hms Htok] as Htok
      · iframe; iframe #
        iapply BigSepL.bigSepL_impl $$ Hms
        imodintro
        iintro %k %m %_ Hm
        iapply (sendMsg_of_netBundle (netRh γn) c.lid m)
        rw [show (netRh γn).γn = γn from rfl]
        iexact Hm
      iapply HΦ
      iexact Htok
    isplitr
    · imodintro
      iintro %Φ !> - HΦ
      wp_apply (rafthttp.Transport.Stop_full hPeerStop hRemoteStop γn t c rs) $$ []
      · iframe #
      iapply HΦ; itrivial
    · imodintro
      iintro %m %ml %rc %Φ !> ⟨Hm, Hb⟩ HΦ
      wp_apply (hSS γn t c rs m ml rc) $$ [Hm Hb]
      · iframe; iframe #
      iapply HΦ; itrivial
  · iunfold rafthttp.isTransporter
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %id %Φ !> - HΦ
    wp_apply (hAS γn t c rs id) $$ [] as %tm -
    · iframe #
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
