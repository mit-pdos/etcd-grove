/-
**The read loop's `server` contract, met by `*EtcdServer`** (`isReadServer`, `read/Inv.lean`;
the request path's unit 4b, 2026-10-13): from the server's persistent views (the proposer's
`isServerReq s E ρ`, the reader's `isServerRead s E γr`) and the specs of its nine methods, the
server value `s` meets the contract the read loop is verified over, with the caller's resource
`LR := srvReadLR s` (the logger's reader slot and the two notifiers' reader slots) and the id
resource `NR := idCred ρ.ids 1` (one id of the generator's budget). Lean-first (no Rocq
counterpart).
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

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`*EtcdServer` meets the read loop's `server` contract** (see the file header). -/
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
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      isReadServer (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s) γr (srvReadLR s)
        (idCred ρ.ids 1) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd⟩
  iunfold isServerReq at Hsrv
  icases Hsrv with ⟨%v, #Hv⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨#Hgenf, #Hgen, -, -, -, -, -, -, -, -, -, -, -, #Hdonef, #Hdone, -, -, -, -, -, -,
    -, %Hcfg⟩
  iunfold isServerRead at Hsrd
  icases Hsrd with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAt at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, -, -, -, #Hlgf, %Hlgn, -, -, -, -, #Hainv, -, #Hawf, #Haw,
    #Hlcf, #Hfcf, #Hstf, #Hst⟩
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
  · iunfold srvChanOk
    iintro !> %Φ !> - HΦ
    wp_apply hStop s w.stopping $$ []
    · iframe #
    iapply HΦ
    iunfold srvDoneChan at Hst
    iunfold bcastChan
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
    iunfold waitBcast at Hch
    iunfold bcastChan
    iframe Hch HQ
  -- `NextRequestID()`
  isplitr
  · iintro !> %Φ !> Hcred HΦ
    wp_apply hNR s v.gen ρ.ids $$ [Hcred] as %id -
    · iframe #; iframe Hcred
    iapply HΦ
    itrivial
  -- `RequestTimeout()`
  · iintro !> %Φ !> - HΦ
    wp_apply hRT s $$ [] as %d -
    · iframe #; ipureintro; exact Hcfg
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
