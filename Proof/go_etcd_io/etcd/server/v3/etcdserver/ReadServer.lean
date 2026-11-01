/-
**The read loop's `server` contract, met by `*EtcdServer`** (`isReadServer`, `read/Inv.lean`;
the request path's unit 4b, 2026-10-13): from the server's persistent views (the proposer's
`isServerReq s E ρ`, the reader's `isServerRead s E γr`) and the specs of its nine methods, the
server value `s` meets the contract the read loop is verified over, with the caller's resource
`LR := srvReadLR s` (the logger's reader slot and the two notifiers' reader slots) and the id
resource `NR := idCred ρ.ids 1` (one id of the generator's budget); and (2026-10-16, stage R7b)
the id's context's fresh token (2026-10-30, the repair: no read credit with it), minted by the server from the id
(`srvRdFresh_mint`, the mint `srvRdFreshInv` in `srvMintInv`), which is why the proposer's names
`ρ` and the reader's `γr` must agree (`ρ.rd = γr`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ApplyWait
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Done
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Stopping
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaderChanged
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__FirstCommitInTermNotify
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__NextRequestID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RequestTimeout
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AppliedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`*EtcdServer` meets the read loop's `server` contract, in either auth mode** (see the file
header; the auth plan's E3r: the views and `AppliedIndex` in the mode). -/
theorem isReadServer_of_serverM (on : Bool)
    (hAW : EtcdServer.ApplyWait.spec (GF := GF) (hG := hG))
    (hDone : EtcdServer.Done.spec (GF := GF) (hG := hG))
    (hStop : EtcdServer.Stopping.spec (GF := GF) (hG := hG))
    (hLC : EtcdServer.LeaderChanged.spec (GF := GF) (hG := hG))
    (hFC : EtcdServer.FirstCommitInTermNotify.spec (GF := GF) (hG := hG))
    (hNR : EtcdServer.NextRequestID.spec (GF := GF) (hG := hG))
    (hRT : EtcdServer.RequestTimeout.spec (GF := GF) (hG := hG))
    (hAI : EtcdServer.AppliedIndex.specM (GF := GF) (hG := hG) on)
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (hρ : ρ.rd = γr) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM on s E ρ ∗ isServerReadM on s E γr ⊢
      isReadServer (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s) γr (srvReadLR s)
        (idCred ρ.ids 1) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd⟩
  ihave ⟨⟨%v, #Hv⟩, #HsrvB⟩ := (isServerReqM_split _ _ _ _).1 $$ Hsrv
  iunfold srvReqFieldsAtM at Hv
  icases Hv with ⟨#Hgenf, #Hgen, -, -, -, -, -, -, -, #Het, #Htm, -, -, #Hdonef, #Hdone, -, -, -, -, -, -,
    #Hm, -, -, -, %HcfgP⟩
  obtain ⟨Hcfg, -⟩ := HcfgP
  iunfold srvMintInv at Hm
  icases Hm with ⟨-, #Hrf⟩
  iunfold isServerReadM at Hsrd
  icases Hsrd with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, -, -, -, #Hlgf, %Hlgn, -, -, -, -, #Hainv, -, -, #Hawf, #Haw,
    #Hlcf, #Hfcf, #Hstf, #Hst, -⟩
  iunfold isReadServer
  -- `Done()`
  isplitr
  · iunfold srvDoneOk
    iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
    isplitr
    · ipureintro; rfl
    iunfold srvChanOk
    iintro !> %Φ !> - HΦ
    wp_apply hDone s v.done $$ []
    · iframe #
    iapply HΦ
    iunfold srvDoneChan at Hdone
    iunfold bcastChan
    iexact Hdone
  iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
  isplitr
  · ipureintro; rfl
  -- `Stopping()`
  isplitr
  · iunfold srvStopOk
    iintro !> %Φ !> - HΦ
    wp_apply hStop s w.stopping $$ []
    · iframe #
    iapply HΦ
    iexact Hst
  -- `LeaderChanged()`
  isplitr
  · iunfold srvChanOkR
    iintro !> %Φ !> HLR HΦ
    iunfold srvReadLR at HLR
    icases HLR with ⟨Hlg, ⟨%n, #Hn, Hr⟩, Hfc⟩
    icombine Hn Hlcf gives %Hnw
    subst Hnw
    wp_apply hLC s w.lc $$ [Hr] as %ch ⟨Hr, #Hch⟩
    · iframe #; iframe Hr
    iapply HΦ
    iunfold notifyChan at Hch
    iunfold bcastChan
    iframe Hch
    iunfold srvReadLR
    iframe Hlg Hfc
    iexists w.lc
    iframe Hlcf Hr
  -- `FirstCommitInTermNotify()`
  isplitr
  · iunfold srvChanOkR
    iintro !> %Φ !> HLR HΦ
    iunfold srvReadLR at HLR
    icases HLR with ⟨Hlg, Hlc, ⟨%n, #Hn, Hr⟩⟩
    icombine Hn Hfcf gives %Hnw
    subst Hnw
    wp_apply hFC s w.fc $$ [Hr] as %ch ⟨Hr, #Hch⟩
    · iframe #; iframe Hr
    iapply HΦ
    iunfold notifyChan at Hch
    iunfold bcastChan
    iframe Hch
    iunfold srvReadLR
    iframe Hlg Hlc
    iexists w.fc
    iframe Hfcf Hr
  -- `Logger()`
  isplitr
  · iintro !> %Φ !> HLR HΦ
    iunfold srvReadLR at HLR
    icases HLR with ⟨Hlg, Hlc, Hfc⟩
    wp_apply hLg s w.lg $$ [Hlg] as ⟨%Hnn, Hlg⟩
    · iframe #; iframe Hlg; ipureintro; exact Hlgn
    iapply HΦ
    isplitr
    · ipureintro; exact Hnn
    iunfold srvReadLR
    iframe
  -- `AppliedIndex()`
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_apply hAI s E γr $$ [] as %i #Hi
    · iframe #
    iapply HΦ
    iexact Hi
  -- `ApplyWait(d)`
  isplitr
  · iintro !> %d %Φ !> - HΦ
    wp_apply hAW s w.aw (appliedAtLeast γr) d $$ [] as %ch ⟨%Q, #Hch, #HQ⟩
    · iframe #
    iapply HΦ
    iexists Q
    iframe HQ
    iunfold waitBcast at Hch
    iunfold bcastOrClosed
    iunfold bcastChan
    iexact Hch
  -- `NextRequestID()`: the id mints its context's token
  isplitr
  · iintro !> %Φ !> #Hcred HΦ
    iapply wp_fupd
    wp_apply hNR s v.gen ρ.ids $$ [] as %id Hfresh
    · iframe #
    imod srvRdFresh_mint ρ.raft ρ.ids v.gen (srvFloorFact E) id $$ Hgen Hcred Hrf Hfresh
      with Hfr
    imodintro
    iapply HΦ
    rw [show ρ.raft = γr.raft by subst hρ; rfl]
    iexact Hfr
  -- `RequestTimeout()`
  · iintro !> %Φ !> - HΦ
    wp_apply hRT s v.electionTicks v.tickMs $$ [] as %d -
    · iframe #
    iapply HΦ
    itrivial

/-- **`*EtcdServer` meets the read loop's `server` contract** (see the file header; at
`on = false`). -/
theorem isReadServer_of_server
    (hAW : EtcdServer.ApplyWait.spec (GF := GF) (hG := hG))
    (hDone : EtcdServer.Done.spec (GF := GF) (hG := hG))
    (hStop : EtcdServer.Stopping.spec (GF := GF) (hG := hG))
    (hLC : EtcdServer.LeaderChanged.spec (GF := GF) (hG := hG))
    (hFC : EtcdServer.FirstCommitInTermNotify.spec (GF := GF) (hG := hG))
    (hNR : EtcdServer.NextRequestID.spec (GF := GF) (hG := hG))
    (hRT : EtcdServer.RequestTimeout.spec (GF := GF) (hG := hG))
    (hAI : EtcdServer.AppliedIndex.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (hρ : ρ.rd = γr) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      isReadServer (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s) γr (srvReadLR s)
        (idCred ρ.ids 1) :=
  isReadServer_of_serverM false hAW hDone hStop hLC hFC hNR hRT hAI hLg s E ρ γr hρ

end proof

end EtcdGrove
end Perennial
