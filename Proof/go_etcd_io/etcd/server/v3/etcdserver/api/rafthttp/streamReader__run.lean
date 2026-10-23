/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamReader__run.lean`.
Lean-first; the reader's goroutine's predicates: `rafthttp/ReaderRun.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__dial
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__decodeLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamType__String_ptr
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__activate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__deactivate
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_etcd_io.etcd.client.pkg.v3.transport.IsClosedConnError
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- A log call (`if cr.lg != nil { cr.lg.Info(...) }` and the like): its fields' strings, the
call. -/
local macro "zap_log" : tactic => `(tactic| (
  repeat' (first
    | (wp_apply hTString _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hZString as %_ -)
    | (wp_apply hZError as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_apply hInfo lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | wp_auto)))

set_option hygiene false in
/-- `if cr.lg != nil { log }`. -/
local macro "lg_log" : tactic => `(tactic| (
  wp_if_destruct
  · exact absurd rfl Hlgnn
  zap_log
  (try wp_auto)))

set_option hygiene false in
/-- The loop's tail: `rl.Wait(ctx)`; if the context is done, the log, `close(cr.done)` and the
return; else the log of `Wait`'s error, if any, and the next round. -/
local macro "run_tail" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hWait rl ctx cd $$ [] as %werr -
  · iframe #
  (try wp_auto)
  wp_apply wp_ctx_Err ctx cd $$ [] as %cerr -
  · iexact Hctx
  rcases cerr with cei | _
  · -- the context is done
    (try wp_auto)
    lg_log
    iunfold srDoneRight at Hdone
    icases Hdone with ⟨%dc, %γdn, #Hdc, Hdb⟩
    (try wp_auto)
    wp_apply (wp_broadcast_chan_close _ γdn iprop(True)) $$ [Hdb] as -
    · iframe; imodintro; itrivial
    wp_for_post
    iapply HΦ; itrivial
  · (try wp_auto)
    rcases werr with wei | _
    · (try wp_auto)
      lg_log
      wp_for_post
      iframe
    · (try wp_auto)
      wp_for_post
      iframe))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem rafthttp.streamReader.run.wp_proof
    (hDial : rafthttp.streamReader.dial.spec (GF := GF) (hG := hG))
    (hDecodeLoop : rafthttp.streamReader.decodeLoop.spec (GF := GF) (hG := hG))
    (hTString : rafthttp.streamType.String_ptr.spec (GF := GF) (hG := hG))
    (hActivate : rafthttp.peerStatus.activate.spec (GF := GF) (hG := hG))
    (hDeactivate : rafthttp.peerStatus.deactivate.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hClosed : transport.IsClosedConnError.spec (GF := GF) (hG := hG))
    (hWait : rate.Limiter.Wait.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG)) :
    rafthttp.streamReader.run.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd cr ty
  wp_start as ⟨#Hf, #Hdial, Hdone⟩
  ihave #Hf' := Hf
  iunfold srFixed at Hf'
  icases Hf' with ⟨%lg, %tr, %ps, %rcc, %pcc, %γr, %γp, %ctx, %cd, #Hlg, %Hlgnn, #Hpid, #Htr,
    #Hlid, #Hps, #Hpsok, -, -, -, -, #Hmu, #Hctxf, #Hctx⟩
  ihave #Hdial' := Hdial
  iunfold srDial at Hdial'
  icases Hdial' with ⟨#Hcfg, -⟩
  iunfold srCfg at Hcfg
  icases Hcfg with ⟨%rl, %pk, %tr', %urls, %uvs, %cid, %rt, %ec, #Htyp, #Hrlf, #Hrl, -, -, -, -,
    -, -, -, -, -, -, -, -⟩
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HUS⟩
  iunfold EtcdGrove.errorsNewVar at HUS
  icases HUS with ⟨%xus, #Hxus, -⟩
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Heof := io.eof_of_init $$ Hio
  iunfold errors.newVar at Heof
  icases Heof with ⟨%xe, #He, -⟩
  ihave #Herrp : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Htrp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.transport $$ []
  · iPkgInit
  ihave #Hratep : isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate $$ []
  · iPkgInit
  (try wp_auto)
  ipersist cr; ipersist t
  lg_log
  ihave IH : iprop("Hdone" ∷ srDoneRight cr) $$ [Hdone]
  · iframe
  wp_for IH
  wp_apply hDial Rh lid pid γd cr ty $$ [] as %rc %err ⟨#Herr, Hres⟩
  · iframe #
  cases err with
  | ok ei =>
    -- the dial failed: the peer status deactivated, unless the stream type is unsupported
    icases Hres with (%Hne | ⟨%Hn, -⟩)
    rotate_left
    · cases Hn
    (try wp_auto)
    wp_apply wp_Is_errStrOk hIs (GoInterface.ok ei) _ (fun _ h => by cases h; exact ⟨_, _, rfl, rfl⟩)
      $$ [] as %b -
    · iframe #
    cases b
    · iunfold http.errStrOk at Herr
      icases Herr with (%Hn | ⟨%e3, %He3, #HE, -⟩)
      · cases Hn
      cases He3
      (try wp_auto)
      zap_log
      wp_apply HE as %es
      (try wp_auto)
      wp_apply hDeactivate ps _ es $$ [$Hpsok]
      run_tail
    · run_tail
  | nil =>
    -- connected: the peer active, the stream decoded until it fails; the status deactivated
    -- unless the stream ended (`io.EOF`) or the connection was closed
    icases Hres with (%Hne | ⟨-, %R, %γk, %γw, %Hown, Hrr, #Hcl, %Hrcnn, #Hreg, Hrd⟩)
    · exact absurd rfl Hne
    (try wp_auto)
    wp_apply hActivate ps $$ [$Hpsok]
    (try wp_auto)
    lg_log
    wp_apply hDecodeLoop Rh lid pid γd cr ty rc R γk γw Hown $$ [$Hrr $Hrd]
      as %derr ⟨%Hdnn, #Hderr⟩
    · iframe #; ipureintro; exact Hrcnn
    (try wp_auto)
    lg_log
    wp_apply wp_Is_errStrOk hIs derr _ (fun _ h => by cases h; exact ⟨_, _, rfl, rfl⟩)
      $$ [] as %b1 -
    · iframe #
    cases b1
    · (try wp_auto)
      wp_apply hClosed derr $$ [] as %b2 -
      · iframe #
      cases b2
      · iunfold http.errStrOk at Hderr
        icases Hderr with (%Hn | ⟨%e3, %He3, #HE, -⟩)
        · exact absurd Hn Hdnn
        subst He3
        (try wp_auto)
        zap_log
        wp_apply HE as %es
        (try wp_auto)
        wp_apply hDeactivate ps _ es $$ [$Hpsok]
        run_tail
      · run_tail
    · run_tail

end proof

end EtcdGrove
end Perennial
