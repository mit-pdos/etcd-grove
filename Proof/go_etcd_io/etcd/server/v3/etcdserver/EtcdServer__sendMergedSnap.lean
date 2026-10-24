/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__sendMergedSnap.lean`. Lean-first
(no Rocq counterpart); D22 S-h, 2026-10-20.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__sendMergedSnap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__GetTo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__CloseNotify
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.github_com.dustin.go_humanize.Bytes
public import Perennial.Spec.sync.atomic.Int64__Add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- `uint64` is not an interface type (as `InvStart.lean`'s: `String()` on a `types.ID`). -/
instance notInterface_uint64_sendMergedSnap [FfiSyntax] : go.NotInterface go.uint64 :=
  ⟨by unfold go.uint64; trivial⟩

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.sendMergedSnap.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hGetTo : snap.Message.GetTo.spec (GF := GF) (hG := hG))
    (hI64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hHB : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (hCN : snap.Message.CloseNotify.spec (GF := GF) (hG := hG))
    (hDur : zap.Duration.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    EtcdServer.sendMergedSnap.spec (GF := GF) (hG := hG) := by
  intro s mg ml rc lg id stg tr γn S
  wp_start as ⟨Hgr, Hlr, #Hlgf, %Hlgnn, #Hidf, #Hinf, #Hstgf, #Hstg, #Htrf, #Htr, #Hmg, Hbun⟩
  ihave #Patm : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  (try wp_auto)
  -- `s.inflightSnapshots.Add(1)`
  wp_apply_core sync.atomic.Int64.wp_Add (srvInflightAddr s) (W64 1) $$ [] [-]
  · iexact Patm
  ihave #Hinf' := Hinf
  iunfold srvInflight at Hinf'
  iinv Hinf' with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  icases Hi with ⟨%v0, Hv⟩
  iexists v0
  iframe Hv
  iintro Hv
  imod Hmask with -
  imod Hclose $$ [Hv] with -
  · inext; iexists _; iexact Hv
  imodintro
  (try wp_auto)
  ihave #Hmg' := Hmg
  iunfold mergedMsg at Hmg'
  icases Hmg' with ⟨#Hmi, %tsz, %cc, %γc, #Htsz, #Hcc, #Hccb⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Phum : isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize $$ []
  · iPkgInit
  ihave #Ptypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  -- the log fields
  wp_apply hLg s lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hMID s id $$ []
  · iframe #
  (try wp_auto)
  wp_apply hIDS as %ids1 -
  wp_apply hStr as %f0 -
  wp_apply hGetTo mg ml rc $$ [] as %to -
  · iframe #
  wp_apply hIDS as %ids2 -
  wp_apply hStr as %f1 -
  (try wp_auto)
  wp_apply hI64 as %f2 -
  (try wp_auto)
  wp_apply hHB as %hb -
  wp_apply hStr as %f3 -
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfsl, Hfcap⟩
  (try wp_auto)
  wp_apply time.wp_Now as %now -
  (try wp_auto)
  -- `s.r.transport.SendSnapshot(merged)`
  ihave #Htr' := Htr
  iunfold netTransport at Htr'
  icases Htr' with ⟨%ti, %Hti, -, -, #Hss⟩
  subst Hti
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"SendSnapshot" ti.v)) (Val #mg))
  iapply Hss $$ [Hbun]
  · iframe Hmi Hbun
  inext
  iintro -
  (try wp_auto)
  -- `lg.Info("sending merged snapshot", fields...)`
  ipersist Hfsl
  ipersist fields
  ipersist now
  ipersist merged
  ipersist lg
  ipersist s
  wp_apply hInfo _ _ _ $$ []
  · iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  -- `s.GoAttach(func() { ... })`: the release goroutine, with the fields' capacity for `append`
  iunfold stopChan at Hstg
  icases Hstg with ⟨%γsg, #Hstg⟩
  wp_apply hGA s _ (ownSliceCap go_uber_org.zap.zapcore.Field _ (DFrac.own 1)) $$ [Hgr Hlr Hfcap]
    as ⟨Hgr, Hlr⟩
  · iframe Hgr Hlr Hfcap
    iintro !> %Φ' Hfcap HΦ'
    wp_auto_lc 2
    wp_apply hCN mg cc $$ []
    · iframe #
    (try wp_auto)
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `ok := <-merged.CloseNotify()`: the send ended
      simp only [chan.blockingClausePre]
      iexists Bool, inferInstance, inferInstance, inferInstance, inferInstance, cc, γc
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hccb
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hccb
      inext
      iintro %ok -
      (try wp_auto)
      -- on a successful send, `releaseDelayAfterSnapshot` or the stop first
      wp_bind (If (Val #ok) _ _)
      iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝)))
      isplitl []
      · cases ok
        · (try wp_auto)
          ipureintro; rfl
        · wp_auto_lc 2
          wp_apply time.wp_After as %tch %γa #Htch
          (try wp_auto)
          wp_apply_core chan.wp_select_blocking
          iapply BigAndL.bigAndL_cons.2
          isplit
          · simp only [chan.blockingClausePre]
            iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γa
            isplitr
            · ipureintro; rfl
            isplitr
            · iapply is_bag_is_chan $$ Htch
            iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
            inext
            iintro %t -
            (try wp_auto)
            ipureintro; rfl
          iapply BigAndL.bigAndL_cons.2
          isplit
          · simp only [chan.blockingClausePre]
            iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stg, γsg
            isplitr
            · ipureintro; rfl
            isplitr
            · iapply ownStopChan_is_chan $$ Hstg
            iapply stop_chan_receive _ _ _ _ _ $$ Hstg
            iintro ⟨-, -⟩
            (try wp_auto)
            ipureintro; rfl
          iapply BigAndL.bigAndL_nil.2
          itrivial
      iintro %v %Hv
      subst Hv
      (try wp_auto)
      -- `s.inflightSnapshots.Add(-1)`
      wp_apply_core sync.atomic.Int64.wp_Add (srvInflightAddr s) (W64 (-1)) $$ [] [-]
      · iexact Patm
      iinv Hinf' with Hi Hclose
      iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
      iintro Hmask
      inext
      icases Hi with ⟨%v1, Hv⟩
      iexists v1
      iframe Hv
      iintro Hv
      imod Hmask with -
      imod Hclose $$ [Hv] with -
      · inext; iexists _; iexact Hv
      imodintro
      (try wp_auto)
      -- `lg.Info("sent merged snapshot", append(fields, zap.Duration("took", time.Since(now)))...)`
      wp_apply time.wp_Since as %d -
      wp_apply hDur as %f4 -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fsl4 ⟨Hf4, -⟩
      (try wp_auto)
      wp_apply wp_slice_append_persistent $$ [Hfcap Hf4] as %fsl5 -
      · iframe Hfsl Hfcap Hf4
      (try wp_auto)
      wp_apply hInfo _ _ _ $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      iapply HΦ'
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-s.stopping`: the server stops, the count is not released
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stg, γsg
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownStopChan_is_chan $$ Hstg
      iapply stop_chan_receive _ _ _ _ _ $$ Hstg
      iintro ⟨-, -⟩
      (try wp_auto)
      wp_apply hWarn _ _ _ $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      iapply HΦ'
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  (try wp_auto)
  iapply HΦ
  iframe Hgr Hlr

end proof

end EtcdGrove
end Perennial
