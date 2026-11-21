/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__RangeStream.lean`. Lean-first (no Rocq
counterpart); auth-mediation M3 (2026-11-21), over the trust boundary `EtcdServer.rangeStream`
(names only) and `doSerialize`'s spec; the model is `EtcdServer.Range`'s proof.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RangeStream
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__rangeStream
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__doSerialize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetKey
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetRangeEnd
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetRevision
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetLimit
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetCountOnly
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_opentelemetry_io.otel.trace.WithAttributes
public import Spec.go_opentelemetry_io.otel.«attribute».String
public import Spec.go_opentelemetry_io.otel.«attribute».Int64
public import Spec.go_opentelemetry_io.otel.«attribute».Bool
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposerLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.StartLaws

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- `get`'s triple: `err = s.rangeStream(ctx, r, rs)` (the trust boundary), at the check `HC` the
caller's chunks carry (`rangeStreamPassed`, persistent). -/
local macro "rs_get" : tactic => `(tactic| (
  wp_auto
  wp_apply (hRS s E ρ γr ctx2 _ trc false r o _ Ψ Ξ) $$ [Hmr Hlr Hown0 HK Hlim Hrev]
    as %errv ⟨Hmr, Hlr, -, Hback, Hres⟩
  · iframe # Hmr Hlr Hown0
    isplitl [HK Hlim Hrev]
    · iunfold rangeRequestOwn
      isplitr
      · ipureintro; exact Hrn
      iexists ksl, esl, k, e, rev0, limit, order, target, ser, ko, co, minM, maxM, minC, maxC
      iframe HK Hlim Hrev
      iframe #
      ipureintro; exact ⟨Ho, Hkb⟩
    isplitr
    · ipureintro; exact Hvst
    iintro !> %resp Hch
    iapply HΨ $$ Hch HC
  wp_auto
  iapply HΦ'
  iexists errv
  iframe err Hmr Hlr Hback
  iexact Hres))

set_option hygiene false in
/-- `doSerialize`'s reason (`HsW0`) as `rangeWhyOut` (`HsW`): `True` with auth off, the check's
refusal at `n` or the revision re-check with auth on (as `Range`'s). -/
local macro "rs_why" : tactic => `(tactic| (
  first
    | (ihave #HsW := rangeWhyOut_off s E.authMode n tok o (GoInterface.ok sei) hon)
    | (ihave %Hel := ownSlice_len _ _ _ $$ Hes
       have he : apply.authEndOf o.base.rangeEnd e := by
         rw [Ho]; simp only [txn.rangeOpOf.proj_base]; exact apply.authEndOf_rangeEndOf esl e Hel.1
       ihave #HsW1 := rangeWhy_of_serialWhy s E.authMode n n (Nat.le_refl _) _ o e he
         (GoInterface.ok sei) (by intro h; cases h) $$ HsW0
       ihave #HsW : rangeWhyOut (GF := GF) s E.authMode n tok o (GoInterface.ok sei) $$ []
       · unfold rangeWhyOut; ileft; iexact HsW1)))

set_option hygiene false in
/-- From `doSerialize`'s result on: its error, or `rangeStream`'s. -/
local macro "rs_out" : tactic => `(tactic| (
  icases Hds with ⟨Hard, (⟨%Hs0, -, %errv, err, Hmr, Hlr, Hback, Hres⟩ |
    ⟨%Hs0, #HsE, HsW0, Hg⟩)⟩
  · subst Hs0
    wp_auto
    wp_apply HEnd
    (try wp_auto)
    iapply HΦ
    isplitl [Hmr Hlr Hrr Hard]
    · iunfold srvRdCall; iframe Hmr Hlr Hcal Hrr Hard
    iframe Hback
    icases Hres with (%He | ⟨%He, #HeE, #HeR⟩ | HΞ)
    · ileft; ipureintro; exact He
    · iright; ileft
      iframe HeE
      isplitr
      · ipureintro; exact He
      iapply rangeWhyOut_of_rangeReadErr $$ HeR
    · iright; iright; iexact HΞ
  · cases serr with
    | nil => exact absurd rfl Hs0
    | ok sei =>
      rs_why
      ihave #HsE1 := authApplyErrIs_apply _ $$ HsE
      icases Hg with (⟨⟨err, Hmr, Hlr, HK, Hlim, Hrev⟩, -⟩ |
        ⟨%errv, err, Hmr, Hlr, Hback, -⟩)
      · wp_auto
        wp_apply HEnd
        (try wp_auto)
        iapply HΦ
        isplitl [Hmr Hlr Hrr Hard]
        · iunfold srvRdCall; iframe Hmr Hlr Hcal Hrr Hard
        isplitl [HK Hlim Hrev]
        · iunfold rangeRequestBack
          iexists ksl, rev0, limit
          iframe HK Hlim Hrev
        iright; ileft
        iframe HsE1 HsW
        ipureintro; intro h; cases h
      · wp_auto
        wp_apply HEnd
        (try wp_auto)
        iapply HΦ
        isplitl [Hmr Hlr Hrr Hard]
        · iunfold srvRdCall; iframe Hmr Hlr Hcal Hrr Hard
        iframe Hback
        iright; ileft
        iframe HsE1 HsW
        ipureintro; intro h; cases h))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem EtcdServer.RangeStream.wp_proof
    (hTS : traceutil.Tracer.Start.spec (GF := GF) (hG := hG))
    (hWA : trace.WithAttributes.spec (GF := GF) (hG := hG))
    (hAS : «attribute».String.spec (GF := GF) (hG := hG))
    (hAI64 : «attribute».Int64.spec (GF := GF) (hG := hG))
    (hAB : «attribute».Bool.spec (GF := GF) (hG := hG))
    (hGK : RangeRequest.GetKey.spec (GF := GF) (hG := hG))
    (hGE : RangeRequest.GetRangeEnd.spec (GF := GF) (hG := hG))
    (hGR : RangeRequest.GetRevision.spec (GF := GF) (hG := hG))
    (hGL : RangeRequest.GetLimit.spec (GF := GF) (hG := hG))
    (hGC : RangeRequest.GetCountOnly.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hET : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hDS : EtcdServer.doSerialize.spec (GF := GF) (hG := hG))
    (hRS : EtcdServer.rangeStream.spec (GF := GF) (hG := hG)) :
    EtcdServer.RangeStream.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr c ctx cd tok r o rs Ψ Ξ ot te n hany
  wp_start as ⟨#Hsrv, #Hrd, #HaLb, #Hpub, Hcall, #HrsC, #Hctx, #Hlib, #HtokC, #Hct, Hto, Hr, %Hvst,
    #Hsend, #HΨ⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hrd' := Hrd
  iunfold isServerReadM at Hrd'
  icases Hrd' with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨#Hread, #HisRead, #Hkvf, #HisKV, %Hkveq0, #Hlef, #Hle, #Hauf, #Hau, #Hlgf,
    #Hlgn, #Hwad, #Hterm, -, #Hainv, #Hkvi, -⟩
  iunfold srvRdCall at Hcall
  icases Hcall with ⟨Hmr, Hlr, #Hcal, Hrr, Hard⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, ⟨%tr, #Htr⟩, -⟩, -⟩
  iunfold rangeRequestOwn at Hr
  icases Hr with ⟨%Hrn, %ksl, %esl, %k, %e, %rev0, %limit, %order, %target, %ser, %ko, %co, %minM,
    %maxM, %minC, %maxC, HK, #Hks, #HE, #Hes, Hlim, Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM,
    #HmaxM, #HminC, #HmaxC, %Ho, %Hkb⟩
  -- `ctx := rs.Context()`
  iunfold rangeStreamCtx at HrsC
  icases HrsC with ⟨%si, %Hsi, #HCtx⟩
  subst Hsi
  wp_auto
  wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
  iapply HCtx
  · itrivial
  iintro !> -
  wp_auto
  -- the span's attributes
  wp_apply hGK r ksl (DFrac.own 1) $$ [HK] as HK
  · iframe #; iframe HK; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [Hks] as -
  · iexact Hks
  (try wp_auto)
  wp_apply hAS as %a1 -
  (try wp_auto)
  wp_apply hGE r esl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [Hes] as -
  · iexact Hes
  (try wp_auto)
  wp_apply hAS as %a2 -
  (try wp_auto)
  wp_apply hGR r rev0 (DFrac.own 1) $$ [Hrev] as Hrev
  · iframe #; iframe Hrev; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hAI64 as %a3 -
  (try wp_auto)
  wp_apply hGL r limit (DFrac.own 1) $$ [Hlim] as Hlim
  · iframe #; iframe Hlim; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hAI64 as %a4 -
  (try wp_auto)
  wp_apply hGC r co $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hAB as %a5 -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨-, -⟩
  (try wp_auto)
  wp_apply hWA as %opt -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨-, -⟩
  (try wp_auto)
  wp_apply (traceutil.Tracer.Start.spec_txn hTS) tr ctx cd _ _ $$ [] as %ctx1 %sp ⟨⟨%vs1, #Hctx1t, Hctx1w⟩, #Hctr1, #Hmd1, #Hsp, -, -, #Hlibw, -⟩
  · iframe #; iunfold mvcc.txnCtx; iright; iexact Hctx
  ihave #Hlib1 := Hlibw $$ Hlib
  iunfold trace.isSpan at Hsp
  icases Hsp with ⟨%si', %Hsi', #HEnd, -, -⟩
  subst Hsi'
  (try wp_auto)
  -- the trace
  wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [Hks] as -
  · iexact Hks
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [Hes] as -
  · iexact Hes
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfl, Hflc⟩
  (try wp_auto)
  wp_apply hET ctx1 _ ot te w.lg _ _ $$ [Hto Hfl Hflc]
    as %ctx2 %trc ⟨⟨%Htrc, -⟩, Hown0, #Hct2, #Hmd2, %vs2, #Hctx2, -, -, #Hlibw2⟩
  · iframe #
    isplitr
    · iapply Hctr1 $$ Hct
    iframe Hto
    iunfold traceutil.ownFields
    iexists _
    iframe Hfl Hflc
    ipureintro
    exact traceutil.fieldsWf_cons_string _ _ _
      (traceutil.fieldsWf_cons_string _ _ _ traceutil.fieldsWf_nil)
  ihave #Hlib2 := Hlibw2 $$ Hlib1
  ihave #HtokC2 : □ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ctx2) tok) $$ []
  · ihave #Htok1 := auth.ctxToken_transfer_gate E.authOn ctx ctx1 tok $$ [$Hmd1 $HtokC]
    iapply auth.ctxToken_transfer_gate E.authOn ctx1 ctx2 tok $$ [$Hmd2 $Htok1]
  (try wp_auto)
  ipersist s
  ipersist r
  ipersist rs
  ipersist ctx
  have Hser : o.base.serializable = ser := by subst Ho; rfl
  ihave #HisRead' := HisRead
  iunfold isReadNotify at HisRead'
  -- `if !r.Serializable { err := s.read.LinearizableReadNotify(ctx); trace.Step(..); if err != nil
  -- { return err } }`
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ trace_ptr ↦ trc ∗ srvReadReader s γr ∗ traceutil.ownTrace trc false ∗
        «$res0_ptr» ↦ GoInterface.nil) ∨
      (∃ rei : GoInterfaceOk, ⌜v = returnVal #()⌝ ∗ trace_ptr ↦ trc ∗ srvReadReader s γr ∗
        traceutil.ownTrace trc false ∗ applyErrIs (GoInterface.ok rei) ∗
        readErrIs (GoInterface.ok rei) ∗ «$res0_ptr» ↦ (GoInterface.ok rei : GoInterface))))
    at next with [Hrr Hown0 trace «$res0»]
  · cases ser
    · -- linearizable: the read index first
      (try wp_auto)
      iunfold srvReadReader at Hrr
      icases Hrr with ⟨%rd, #Hrd0, Hrr⟩
      icombine Hread Hrd0 gives %Hrdeq
      subst Hrdeq
      imod saved_pred_alloc (fun _ : List EntryModel => iprop(True : IProp GF)) DFrac.discard trivial
        with ⟨%g, #Hg⟩
      wp_apply HisRead' $$ %ctx2 %_ %c %g %(fun _ : List EntryModel => iprop(True : IProp GF)) [Hrr]
        as %rerr ⟨Hrr, #HrE, #HrdE, -⟩
      · iframe #; iframe Hrr
      ihave Hrr : srvReadReader s γr $$ [Hrr]
      · iunfold srvReadReader; iexists _; iframe Hread Hrr
      (try wp_auto)
      wp_apply hStep trc false _ slice.nil $$ [$Hown0] as Hown0
      · iapply traceutil.ownFields_nil
      (try wp_auto)
      cases rerr with
      | ok rei =>
        wp_auto
        iright
        iexists rei
        isplitr
        · ipureintro; rfl
        iframe trace Hrr Hown0 HrE HrdE «$res0»
      | nil =>
        wp_auto
        ileft
        isplitr
        · ipureintro; rfl
        iframe trace Hrr Hown0 «$res0»
    · (try wp_auto)
      ileft
      isplitr
      · ipureintro; rfl
      iframe trace Hrr Hown0 «$res0»
  iintro (⟨%Hv, trace, Hrr, Hown0, «$res0»⟩ |
    ⟨%rei, %Hv, trace, Hrr, Hown0, #HrE, #HrdE, «$res0»⟩)
  rotate_left
  · -- the read index's error: return it
    subst Hv
    wp_auto
    wp_apply HEnd
    (try wp_auto)
    iapply HΦ
    isplitl [Hmr Hlr Hrr Hard]
    · iunfold srvRdCall; iframe Hmr Hlr Hcal Hrr Hard
    isplitl [HK Hlim Hrev]
    · iunfold rangeRequestBack
      iexists ksl, rev0, limit
      iframe HK Hlim Hrev
    iright; ileft
    iframe HrE
    isplitr
    · ipureintro; intro h; cases h
    iapply rangeWhyOut_read s E.authMode n tok o _ $$ HrdE
  subst Hv
  wp_auto
  -- the two modes differ in the check (`chk`) only
  cases hon : E.authOn
  · -- auth off
    have hMoff : E.authMode = .off := by
      unfold apply.AEnv.authOn at hon
      cases hM : E.authMode <;> simp_all [auth.AuthMode.isOn]
    ihave #Hau' := Hau
    iunfold apply.isAuthStore at Hau'
    icases Hau' with ⟨%aui, %Haui, -, #HIRP, -⟩
    iunfold apply.permCheck3 at HIRP
    have hDS := hDS s E ρ γr ctx2 _ tok
    rw [hon] at hDS
    wp_apply (hDS _ _
      iprop(err_ptr ↦ GoInterface.nil ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvLgReader s ∗
        structFieldRef etcdserverpb.RangeRequest go!"Key" r ↦ ksl ∗
        structFieldRef etcdserverpb.RangeRequest go!"Limit" r ↦ limit ∗
        structFieldRef etcdserverpb.RangeRequest go!"Revision" r ↦ rev0)
      iprop(∃ errv : GoInterface, err_ptr ↦ errv ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvLgReader s ∗
        rangeRequestBack r ∗
        (⌜errv = GoInterface.nil⌝ ∨ (⌜errv ≠ GoInterface.nil⌝ ∗ applyErrIs errv ∗ rangeReadErr errv) ∨
          ∃ resp : Loc, Ξ resp errv))
      (fun info => apply.rangeClass E.authMode info o) (fun _ _ => iprop(True)) trc false n)
        $$ [err Hmr Hlr HK Hlim Hrev Hown0 Hard] as %serr Hds
    · iframe #
      isplitr
      · iintro !>; iexact Hpub
      isplitr
      · iintro %a %info %dq !> %Φ' ⟨Ha, Hard, ⟨err, Hmr, Hlr, HK, Hlim, Hrev⟩⟩ HΦ'
        wp_auto
        rw [Haui]
        (try wp_auto)
        wp_bind (App (App (App (Val _) (Val #a)) (Val #ksl)) (Val #esl))
        iapply HIRP $$ [Ha Hard]
        · iframe Ha Hks Hes Hard; ipureintro; exact Hkb
        inext
        iintro %perr ⟨Ha, -, -, Hard, #HpE0, -, #Hpv⟩
        wp_auto
        iapply HΦ'
        iframe Ha Hard HpE0 err Hmr Hlr HK Hlim Hrev
        isplitl []
        · iintro %Hpn
          subst Hpn
          ihave %Hel := ownSlice_len _ _ _ $$ Hes
          unfold apply.rangeClass
          iexists e
          isplitl []
          · ipureintro; rw [Ho]; simp only [txn.rangeOpOf.proj_base]
            exact apply.authEndOf_rangeEndOf esl e Hel.1
          · rw [Ho]; simp only [txn.rangeOpOf.proj_key]
            iapply (apply.classRes_of_permVerdict E.authMode info k e .read) $$ Hpv
        · iintro %_; itrivial
      isplitr
      · iintro !> %Φ' ⟨⟨err, Hmr, Hlr, HK, Hlim, Hrev⟩, Hown0, %infoc, #Hcls, #Hib⟩ HΦ'
        ihave #HC : rangeStreamPassed s E n tok o $$ []
        · iunfold rangeStreamPassed
          iexists infoc, n
          rw [hMoff]
          isplitr
          · ipureintro; exact Nat.le_refl _
          isplitl []
          · iapply apply.rangeClassFrom_off n infoc o $$ Hcls
          iframe Hib
          unfold auth.authPubLbM; ipureintro; trivial
        rs_get
      iframe
    rs_out
  · -- auth on
    obtain ⟨γa, hM⟩ : ∃ γa, E.authMode = .on γa := by
      unfold apply.AEnv.authOn at hon
      cases hM : E.authMode with
      | off => simp_all [auth.AuthMode.isOn]
      | any => exact absurd hM hany
      | on γa => exact ⟨γa, rfl⟩
    -- the store's range check at the reader's lower bound `n`
    ihave #HaLbS := HaLb
    iunfold srvAuthLb at HaLb
    icases HaLb with ⟨%au, #Hauf2, #HLb⟩
    icombine Hauf Hauf2 gives %Hau2
    subst Hau2
    ihave #HLb' : iprop(□ ∀ n : Nat, auth.authPubLbM (.on γa) n -∗
        apply.isAuthStoreRangeLbR w.auth E.RD (.on γa) n) $$ []
    · iapply authStoreLbM_rangeR γa w.auth E.RD
      rw [← hM]; iexact HLb
    ihave #Hpub' : auth.authPubLbM (GF := GF) (.on γa) n $$ []
    · rw [← hM]; iexact Hpub
    ihave #Hau' := HLb' $$ %n Hpub'
    iunfold apply.isAuthStoreRangeLbR at Hau'
    icases Hau' with ⟨%aui, %Haui, #HIRP⟩
    iunfold apply.permCheck3LbR at HIRP
    have hDS := hDS s E ρ γr ctx2 _ tok
    rw [hon] at hDS
    wp_apply (hDS _ _
      iprop(err_ptr ↦ GoInterface.nil ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvLgReader s ∗
        structFieldRef etcdserverpb.RangeRequest go!"Key" r ↦ ksl ∗
        structFieldRef etcdserverpb.RangeRequest go!"Limit" r ↦ limit ∗
        structFieldRef etcdserverpb.RangeRequest go!"Revision" r ↦ rev0)
      iprop(∃ errv : GoInterface, err_ptr ↦ errv ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvLgReader s ∗
        rangeRequestBack r ∗
        (⌜errv = GoInterface.nil⌝ ∨ (⌜errv ≠ GoInterface.nil⌝ ∗ applyErrIs errv ∗ rangeReadErr errv) ∨
          ∃ resp : Loc, Ξ resp errv))
      (fun info => apply.rangeClassFrom E.authMode n info o)
      (fun info err => auth.permRefusalM E.authMode n info o.key e .read err) trc false n)
        $$ [err Hmr Hlr HK Hlim Hrev Hown0 Hard] as %serr Hds
    · iframe #
      isplitr
      · iintro !>; iexact Hpub
      isplitr
      · iintro %a %info %dq !> %Φ' ⟨Ha, Hard, ⟨err, Hmr, Hlr, HK, Hlim, Hrev⟩⟩ HΦ'
        wp_auto
        rw [Haui]
        (try wp_auto)
        wp_bind (App (App (App (Val _) (Val #a)) (Val #ksl)) (Val #esl))
        iapply HIRP $$ [Ha Hard]
        · iframe Ha Hks Hes Hard; ipureintro; exact Hkb
        inext
        iintro %perr ⟨Ha, -, -, Hard, #HpE0, #Hpv, #Hpr⟩
        wp_auto
        iapply HΦ'
        iframe Ha Hard HpE0 err Hmr Hlr HK Hlim Hrev
        isplitr
        · iintro %Hpn
          subst Hpn
          ihave %Hel := ownSlice_len _ _ _ $$ Hes
          unfold apply.rangeClassFrom
          iexists e
          isplitl []
          · ipureintro; rw [Ho]; simp only [txn.rangeOpOf.proj_base]
            exact apply.authEndOf_rangeEndOf esl e Hel.1
          · rw [Ho, hM]; simp only [txn.rangeOpOf.proj_key]
            iexact Hpv
        · iintro %_
          rw [Ho, hM]; simp only [txn.rangeOpOf.proj_key]
          iexact Hpr
      isplitr
      · iintro !> %Φ' ⟨⟨err, Hmr, Hlr, HK, Hlim, Hrev⟩, Hown0, %infoc, #Hcls, #Hib⟩ HΦ'
        ihave #HC : rangeStreamPassed s E n tok o $$ []
        · iunfold rangeStreamPassed
          iexists infoc, n
          isplitr
          · ipureintro; exact Nat.le_refl _
          iframe Hcls Hib Hpub
        rs_get
      iframe
    rs_out

end proof

end EtcdGrove
end Perennial
