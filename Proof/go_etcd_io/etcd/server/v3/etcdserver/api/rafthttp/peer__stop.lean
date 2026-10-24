/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/peer__stop.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline__stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotSender__stop
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String

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
/-- A log call: `p.id.String()`, the call. -/
local macro "ps_log" : tactic => `(tactic| (
  repeat' (first
    | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hZString as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hInfo lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_if_destruct; (try (exfalso; exact Hlgnn rfl)))
    | wp_auto)))

set_option maxHeartbeats 4000000 in
theorem rafthttp.peer.stop.wp_proof
    (hSWStop : rafthttp.streamWriter.stop.spec (GF := GF) (hG := hG))
    (hPipeStop : rafthttp.pipeline.stop.spec (GF := GF) (hG := hG))
    (hSRStop : rafthttp.streamReader.stop.spec (GF := GF) (hG := hG))
    (hSnapStop : rafthttp.snapshotSender.stop.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG)) :
    rafthttp.peer.stop.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd R p
  wp_start as ⟨#Hp, Hst⟩
  iunfold peerOk at Hp
  icases Hp with ⟨%lg, %ps, %pk, %cw2, %cw1, %pl, %ss, %cr2, %cr1, %r, %rc, %pc, #Hlg, %Hlgnn,
    #Hlid, #Hpid, -, -, -, -, -, -, #Hcw2, #Hf2, #Hcw1, #Hf1, #Hpl, -, #Hss, -, #Hcr2, #Hsr2, #Hst2,
    #Hcr1, #Hsr1, #Hst1, -, -, -⟩
  iunfold peerStop at Hst
  icases Hst with ⟨%cw2', %cw1', %pl', %ss', %sc, %γs, %cf, %γc, #Hsc, Hsb, #Hcf, #Hcancel,
    #Hcw2', Hsw2, #Hcw1', Hsw1, #Hpl', Hpls, #Hss', Hsns⟩
  icombine Hcw2 Hcw2' gives %E2
  icombine Hcw1 Hcw1' gives %E1
  icombine Hpl Hpl' gives %E3
  icombine Hss Hss' gives %E4
  subst E2 E1 E3 E4
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  ps_log
  wp_apply (wp_broadcast_chan_close _ γs iprop(True)) $$ [Hsb] as -
  · iframe; imodintro; itrivial
  (try wp_auto)
  iunfold context.cancelSpec at Hcancel
  wp_apply Hcancel
  · imodintro; itrivial
  iintro -
  (try wp_auto)
  wp_apply hSWStop Rh .msgAppV2 lid pid R cw2 $$ [Hsw2]
  · iframe #; iframe
  (try wp_auto)
  wp_apply hSWStop Rh .message lid pid R cw1 $$ [Hsw1]
  · iframe #; iframe
  (try wp_auto)
  wp_apply hPipeStop Rh pl pid R $$ [Hpls] as ⟨HR1, HR2, HR3, HR4⟩
  · iframe #; iframe
  (try wp_auto)
  wp_apply hSnapStop ss $$ [Hsns]
  · iframe #; iframe
  (try wp_auto)
  wp_apply hSRStop Rh lid pid γd cr2 $$ []
  · iframe #
  (try wp_auto)
  wp_apply hSRStop Rh lid pid γd cr1 $$ []
  · iframe #
  (try wp_auto)
  ps_log
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
