/-
**The transport's methods over its state** (rafthttp stage 6d; D43 M5c): `AddPeer` and `Stop`
(`Stop_live`) on a live transport (`trLive`); `AddRemote` (of an id of the pool's `L`), `Send`,
`CutPeer` and `MendPeer` (of an id not in `L`) on a started one (`trState`), the read-locked ones
with a reader's token (`trTok`); `Stop` and `Handler` on a frozen one (`trFrozen`); a frozen
transport as the network's (`trFrozen_net`: `netTransport` with a free `Stop`, `isTransporter`),
and a started one (`trState_net`: `netTransport` whose `Stop` takes the live right). Lean-first.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- **`t.AddPeer(id, us)` of a frozen peer, with the stop token** (D43 M5e, 2026-10-26,
`AddPeer_frozen`): the transport not stopped (the token) and `id` one of its peers, it returns at
once. -/
theorem rafthttp.Transport.AddPeer_frozen (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds)
    (id : w64) (us : GoSlice) (Hid : id ∈ rs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFrozen γn t c rs ∗ trFrozenTok c.γr rs }}
      (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddPeer")) (Val #id))
        (Val #us))
    {{ RET #(); trFrozenTok c.γr rs }} := by
  wp_start_folded as ⟨#Hf, Htk⟩
  iunfold trFrozen at Hf
  icases Hf with ⟨#Hst, -⟩
  tr_state Hst
  iunfold trFrozenTok at Htk
  wp_apply (rafthttp.Transport.AddPeer_known_core (netRh γn) t c.lid c.γd c.R c.γs c.γr rs _ id us
    Hid) $$ [Htk] as Htk
  · iframe #; iframe
  iapply HΦ
  iunfold trFrozenTok
  iexact Htk

/-- **`t.AddPeer(id, us)` of a live peer** (D43 M5e, 2026-10-26, the user's `AddPeer_known`): on a
live transport, of an id among its peers, it returns at once, nothing changed. -/
theorem rafthttp.Transport.AddPeer_known (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds)
    (id : w64) (us : GoSlice) (Hid : id ∈ rs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trLive γn t c rs }}
      (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddPeer")) (Val #id))
        (Val #us))
    {{ RET #(); trLive γn t c rs }} := by
  wp_start_folded as Hl
  iunfold trLive at Hl
  icases Hl with ⟨#Hst, Hg⟩
  ihave #Hst' := Hst
  tr_state Hst'
  wp_apply (rafthttp.Transport.AddPeer_known_core (netRh γn) t c.lid c.γd c.R c.γs c.γr rs _ id us
    Hid) $$ [Hg] as Hg
  · iframe #; iframe
  iapply HΦ
  iunfold trLive
  iframe Hst Hg

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
    {{ RET #(); trLive γn t c (rs ++ [id]) ∗ us ↦*{dq} ss }} := by
  wp_start_folded as ⟨Hl, Hus, HRs⟩
  iunfold trLive at Hl
  icases Hl with ⟨#Hst, Hg⟩
  ihave #Hst' := Hst
  tr_state Hst'
  wp_apply (rafthttp.Transport.AddPeer_core hNewURLs hFollower hStartPeer hProber hIDString
      hIDStringPtr hInfo hZString hZStrings (netRh γn) t c.lid c.γd c.R c.γs c.γr c.L rs id us dq ss
      Hne Hpl Hown Hself Hpm) $$ [Hg Hus HRs] as ⟨Hg, Hus⟩
  · iframe; iframe #
  iapply HΦ
  iframe
  iunfold trLive
  iframe #
  iexact Hg

/-- **`t.AddRemote(id, us)`** on a started transport (D43 M5c: any caller, no owner's right), as
`AddPeer`, of an id the pool has four `R`s for (`id ∈ c.L`): it returns. -/
theorem rafthttp.Transport.AddRemote_full
    (hNewURLs : types.NewURLs.spec (GF := GF) (hG := hG))
    (hStartRemote : rafthttp.startRemote.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZStrings : zap.Strings.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (id : w64) (us : GoSlice) (dq : DFrac)
    (ss : List GoString) (Hne : ss ≠ []) (Hpl : ∀ s ∈ ss, types.plainPeerURL s)
    (Hown : ∀ h, go!"http://" ++ h ∈ ss → (netRh γn).owner h = id) (Hself : c.lid ≠ id)
    (Hpm : (netRh γn).member id) (HL : id ∈ c.L) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trState γn t c ∗ us ↦*{dq} ss }}
      (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddRemote"))
        (Val #id)) (Val #us))
    {{ RET #(); us ↦*{dq} ss }} := by
  wp_start_folded as ⟨#Hst, Hus⟩
  tr_state Hst
  wp_apply (rafthttp.Transport.AddRemote_core hNewURLs hStartRemote hIDStringPtr hInfo hZString
      hZStrings (netRh γn) t c.lid c.γd c.R c.γs c.γr c.L id us dq ss Hne Hpl Hown Hself Hpm HL)
    $$ [Hus] as Hus
  · iframe; iframe #
  iapply HΦ
  iframe

/-- **`t.CutPeer(id)`** on a started transport with a reader's token, `id` never a remote (not
among the pool's ids `c.L`). -/
theorem rafthttp.Transport.CutPeer_full [PeerPausable] (hM : rafthttp.peer.Pause.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (id : w64) (Hid : id ∉ c.L) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trState γn t c ∗ trTok γn t c }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"CutPeer")) (Val #id))
    {{ RET #(); trTok γn t c }} := by
  wp_start_folded as ⟨#Hst, Htok⟩
  tr_state Hst
  iunfold trTok at Htok
  wp_apply (rafthttp.Transport.CutPeer_core hM (netRh γn) t c.lid c.γd c.R c.γs c.γr c.L id Hid)
    $$ [Htok] as Htok
  · iframe; iframe #
  iapply HΦ
  iunfold trTok
  iexact Htok

/-- **`t.MendPeer(id)`**, as `CutPeer`. -/
theorem rafthttp.Transport.MendPeer_full [PeerPausable] (hM : rafthttp.peer.Resume.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (id : w64) (Hid : id ∉ c.L) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trState γn t c ∗ trTok γn t c }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"MendPeer")) (Val #id))
    {{ RET #(); trTok γn t c }} := by
  wp_start_folded as ⟨#Hst, Htok⟩
  tr_state Hst
  iunfold trTok at Htok
  wp_apply (rafthttp.Transport.MendPeer_core hM (netRh γn) t c.lid c.γd c.R c.γs c.γr c.L id Hid)
    $$ [Htok] as Htok
  · iframe; iframe #
  iapply HΦ
  iunfold trTok
  iexact Htok

/-- **`t.Stop()`** on a frozen transport, with its stop token (D43 M5e): it returns. -/
theorem rafthttp.Transport.Stop_full
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFrozen γn t c rs ∗ trFrozenTok c.γr rs }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Stop")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨#Hf, Htk⟩
  iunfold trFrozen at Hf
  icases Hf with ⟨#Hst, #Hfr⟩
  tr_state Hst
  wp_apply (rafthttp.Transport.Stop_core hPeerStop hRemoteStop (netRh γn) t c.lid c.γd c.R c.γs
    c.γr c.L) $$ [Htk]
  · iframe #
    iintro %rs' %sb Hg
    imod trRemotes_agree c.γr rs rs' sb _ $$ Hfr Hg with ⟨Hg, %Heq⟩
    subst Heq
    iapply trRemotes_stop c.γr _ sb $$ Hfr Htk Hg
  iapply HΦ; itrivial

/-- **`t.Stop()`** on a live transport (D43 M5c, `Stop_live`): it returns, the owner's right
consumed (the transport marked stopped: no `AddPeer` after it). -/
theorem rafthttp.Transport.Stop_live
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trLive γn t c rs }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Stop")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as Hl
  iunfold trLive at Hl
  icases Hl with ⟨#Hst, Hg⟩
  tr_state Hst
  wp_apply (rafthttp.Transport.Stop_core hPeerStop hRemoteStop (netRh γn) t c.lid c.γd c.R c.γs
    c.γr c.L) $$ [Hg]
  · iframe #
    iintro %rs' %sb Hg'
    ihave %Hag := ghostVar_agree c.γr _ _ _ _ $$ Hg Hg'
    cases Hag
    imod ghostVar_update_halves (rs, true) c.γr _ _ $$ Hg Hg' with ⟨-, Hg'⟩
    imodintro
    iexact Hg'
  iapply HΦ; itrivial

/-- **`t.Send(msgs)`** on a started transport with a reader's token, of messages the member sends
(`sendMsg`): the peers and remotes read under the lock (D43 M5c: a message to an id that is
neither is dropped). -/
theorem rafthttp.Transport.Send_full (hSend : rafthttp.Transport.Send.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (sl : GoSlice) (msL : List Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trState γn t c ∗ trTok γn t c ∗ sl ↦* msL ∗
        [∗list] m ∈ msL, sendMsg (netRh γn) c.lid m }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Send")) (Val #sl))
    {{ RET #(); trTok γn t c }} := by
  wp_start_folded as ⟨#Hst, Htok, Hsl, Hms⟩
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
    (hSnServe : rafthttp.snapshotHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (hARR : rafthttp.addRemoteFromRequest.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (a : GoString)
    (Hown : (netRh γn).owner a = c.lid)
    (Hcov : ∀ f, (netRh γn).member f → f ≠ c.lid → f ∈ rs) :
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
  wp_apply (rafthttp.Transport.Handler_core hNPH hNSH hNSnH hNewHandler hGet hPServe hSServe hSnServe
      (netRh γn) t c.lid c.γd c.R c.γs c.γr a sst Rm Hown) $$ [] as %h Hh
  · iframe #
    rw [show (netRh γn).γn = γn from rfl]
    iexact Hdir
  iapply HΦ
  iunfold trTok
  iexact Hh

/-- **A started transport is the network's** (stage 6d; D43 M5c): `netTransport` of its member,
its `Send` borrowing a reader's token (`Send_full`, each message's bundle with its encoding's
bound, `sendMsg_of_netBundle`), its `Stop` taking `TS`, which gives the transport's `Stop`
(`hStop`), and `SendSnapshot` (`hSS`); and its `ActiveSince` (`isTransporter`). -/
theorem trState_net_gen (hSend : rafthttp.Transport.Send.spec (GF := GF) (hG := hG))
    (hSS : rafthttp.Transport.SendSnapshot.spec (GF := GF) (hG := hG))
    (hAS : rafthttp.Transport.ActiveSince.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (TS : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trState γn t c ∗
        □ {{ TS }} (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Stop"))
          (Val #())) {{ RET #(); True }} ⊢
      netTransport γn c.lid (interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t)
          (trTok γn t c) TS ∗
        rafthttp.isTransporter (interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t) := by
  iintro ⟨#Hpkg, #Hst, #hStop⟩
  isplitr
  · iunfold netTransport
    iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · imodintro
      iintro %sl %msL %Φ !> ⟨Hsl, Hms, Htok⟩ HΦ
      wp_apply (rafthttp.Transport.Send_full hSend γn t c sl msL) $$ [Hsl Hms Htok] as Htok
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
    · iexact hStop
    · imodintro
      iintro %m %ml %rc %Φ !> ⟨Hm, Hb⟩ HΦ
      wp_apply (hSS γn t c m ml rc) $$ [Hm Hb]
      · iframe; iframe #
      iapply HΦ; itrivial
  · iunfold rafthttp.isTransporter
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %id %Φ !> - HΦ
    wp_apply (hAS γn t c id) $$ [] as %tm -
    · iframe #
    iapply HΦ; itrivial

/-- **A frozen transport is the network's** (stage 6d): `trState_net_gen` with `Stop` taking the
frozen transport's stop token (`Stop_full`; D43 M5e, 2026-10-26, the user's (B): until then free). -/
theorem trFrozen_net (hSend : rafthttp.Transport.Send.spec (GF := GF) (hG := hG))
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (hSS : rafthttp.Transport.SendSnapshot.spec (GF := GF) (hG := hG))
    (hAS : rafthttp.Transport.ActiveSince.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFrozen γn t c rs ⊢
      netTransport γn c.lid (interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t)
          (trTok γn t c) (trFrozenTok c.γr rs) ∗
        rafthttp.isTransporter (interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t) := by
  iintro ⟨#Hpkg, #Hf⟩
  ihave #Hf' := Hf
  iunfold trFrozen at Hf'
  icases Hf' with ⟨#Hst, -⟩
  iapply trState_net_gen hSend hSS hAS γn t c (trFrozenTok c.γr rs)
  iframe #
  iintro !> %Φ !> Htk HΦ
  wp_apply (rafthttp.Transport.Stop_full hPeerStop hRemoteStop γn t c rs) $$ [Htk]
  · iframe #; iframe
  iapply HΦ; itrivial

/-- **A started transport is the network's, its `Stop` the live right's** (D43 M5c, the user's
(A)): `Stop` takes `trLive` (`Stop_live`), which the owner (the apply thread, in the dynamic mode)
hands over when it stops adding peers. -/
theorem trState_net (hSend : rafthttp.Transport.Send.spec (GF := GF) (hG := hG))
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (hSS : rafthttp.Transport.SendSnapshot.spec (GF := GF) (hG := hG))
    (hAS : rafthttp.Transport.ActiveSince.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trState γn t c ⊢
      netTransport γn c.lid (interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t)
          (trTok γn t c) iprop(∃ rs : trIds, trLive γn t c rs) ∗
        rafthttp.isTransporter (interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t) := by
  iintro ⟨#Hpkg, #Hst⟩
  iapply trState_net_gen hSend hSS hAS γn t c iprop(∃ rs : trIds, trLive γn t c rs)
  iframe #
  iintro !> %Φ !> ⟨%rs, Hl⟩ HΦ
  wp_apply (rafthttp.Transport.Stop_live hPeerStop hRemoteStop γn t c rs) $$ [Hl]
  · iframe
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
