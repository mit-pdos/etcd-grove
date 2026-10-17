/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__streamClientInterceptor.lean` (etcd-io/etcd#21739,
pr-verify). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__streamClientInterceptor
public import Spec.go_etcd_io.etcd.client.v3.reuseOrNewWithCallOptions
public import Spec.go_etcd_io.etcd.client.v3.withVersion
public import Spec.go_etcd_io.etcd.client.v3.Client__getToken
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_etcd_io.etcd.client.v3.filterCallOptions
public import Spec.google_golang_org.grpc.status.Errorf
public import Spec.go_etcd_io.etcd.client.v3.isContextError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- A context a client call takes: its `Err()` returns some error. -/
theorem wp_ctxOk_Err (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (Φ : val → IProp GF) :
    ctxOk ci cd -∗ ▷ (∀ e : GoInterface, Φ #e) -∗
      WP (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #())) {{ Φ }} := by
  iintro #HC HΦ
  iunfold ctxOk at HC
  icases HC with (#HC | #HQ)
  · iunfold _root_.Perennial.context.isContext at HC
    iunfold _root_.Perennial.context.isContextDef at HC
    iNamed HC
    wp_apply HErr $$ %Broadcast.Pending as %ce -
    iapply HΦ
  · iunfold ctxQuiet at HQ
    iapply HQ
    inext
    iapply HΦ

theorem Client.streamClientInterceptor.wp_proof
    (wp_reuse : reuseOrNewWithCallOptions.spec (GF := GF) (hG := hG))
    (wp_withVersion : withVersion.spec (GF := GF) (hG := hG))
    (wp_getToken : Client.getToken.spec (GF := GF) (hG := hG))
    (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG))
    (wp_zapError : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (wp_filter : filterCallOptions.spec (GF := GF) (hG := hG))
    (wp_Errorf : status.Errorf.spec (GF := GF) (hG := hG))
    (wp_isContextError : isContextError.spec (GF := GF) (hG := hG)) :
    Client.streamClientInterceptor.spec (GF := GF) (hG := hG) := by
  intro c sl ros
  wp_start as ⟨#Hc, #Hsl, #Hros⟩
  ihave Hci : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, ⟨%dp, %dov, #Hdp, #Hdov, #Hdbf⟩⟩
  wp_auto
  ipersist c
  wp_apply_raw wp_reuse dp sl ros $$ []
  · iframe #
    unfold retryOptsAt
    iexists dov
    iframe #
    unfold optionsOk
    iexact Hdbf
  inext
  iintro %io #Hio
  wp_pures
  wp_alloc intOpts_ptr as intOpts
  wp_pures
  wp_store
  ipersist intOpts
  wp_auto
  rw [recv_eq_func_mk]
  iapply HΦ
  unfold etcdStreamInterceptorOk
  iintro !> %ctx %cd %desc %dv %cc %method %st %opts %vs %Ψ !>
    ⟨#Hctx, #Hdesc, #Hst, #Hopts, #Hok⟩ HΨ
  (try wp_auto)
  wp_apply wp_withVersion ctx cd $$ [$Hctx] as %c' ⟨%ci, %vsv, %Hc', #Hctx'⟩
  subst Hc'
  (try wp_auto)
  wp_apply wp_getToken c ci { cd with Values := vsv } $$ [$Hc $Hctx'] as %terr #Hterr
  ihave #Hc' := Hc
  iunfold retryClientOk at Hc'
  icases Hc' with ⟨%Hcn, #Hlg, -⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  cases terr with
  | ok te =>
    iunfold clientErrOk at Hterr
    icases Hterr with ⟨-, #Hse⟩
    (try wp_auto)
    wp_apply wp_isContextError (GoInterface.ok te) $$ [$Hse] as %b1 -
    cases b1
    · -- not a context error: the log
      (try wp_auto)
      wp_apply wp_zapError as %f1 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply wp_GetLogger c $$ [$Hlg] as %lg %Hlgn
      wp_apply wp_Error lg _ _ $$ []
      · iframe #; ipureintro; exact Hlgn
      (try wp_auto)
      iapply HΨ; itrivial
    · (try wp_auto)
      wp_bind (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #()))
      iapply wp_ctxOk_Err $$ Hctx'
      inext
      iintro %e
      cases e with
      | ok ei =>
        (try wp_auto)
        iapply HΨ; itrivial
      | nil =>
        (try wp_auto)
        wp_apply wp_zapError as %f1 -
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply wp_GetLogger c $$ [$Hlg] as %lg %Hlgn
        wp_apply wp_Error lg _ _ $$ []
        · iframe #; ipureintro; exact Hlgn
        (try wp_auto)
        iapply HΨ; itrivial
  | nil =>
  (try wp_auto)
  wp_apply wp_filter opts vs $$ [$Hopts $Hok] as %g %r ⟨%gs, %ros', Hg, Hgc, %Hgs, Hr, #Hros'⟩
  (try wp_auto)
  ipersist Hg
  ipersist Hr
  ihave #Hros'' : iprop([∗list] ro ∈ ros', optApplyOk (GF := GF) ro.applyFunc') $$ []
  · iapply (BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := ros')
      (Φ := fun _ (ro : go_etcd_io.etcd.client.v3.retryOption) => retryApplyOk (GF := GF) ro.applyFunc')
      (Ψ := fun _ ro => optApplyOk (GF := GF) ro.applyFunc')
      (fun {_ ro} => optApplyOk_of_retryApplyOk ro.applyFunc'))
    iexact Hros'
  wp_apply wp_reuse io r ros' $$ [] as %co #Hco
  · iframe #
  ihave #Hco' := Hco
  iunfold retryOptsAt at Hco'
  icases Hco' with ⟨%cov, #Hcov, #Hcovk⟩
  icases options_fields_ro co cov $$ Hcov with ⟨#Hrp, #Hmax, #Hbf, #Hra⟩
  iunfold grpcStreamerOk at Hst
  ihave #Hdesc' := Hdesc
  iStructNamed Hdesc'
  (try wp_auto)
  wp_if_destruct
  · -- `callOpts.max == 0`: the streamer's stream
    (try wp_auto)
    wp_apply Hst $$ %ci %{ cd with Values := vsv } %desc %cc %method %g %gs [] as %cs %serr -
    · iframe #
    (try wp_auto)
    iapply HΨ; itrivial
  (try wp_auto)
  generalize dv.ClientStreams' = bcs
  cases bcs
  rotate_left
  · -- `desc.ClientStreams`: `Unimplemented`
    (try wp_auto)
    wp_apply wp_Errorf (W32 12) _ _ $$ [] as %e -
    · ihave #Hst' : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
      · iPkgInit
      iframe #
      ipureintro
      intro h
      have h' : (W32 12) = W32 0 := go.intoVal_inj h
      exact absurd h' (by decide)
    (try wp_auto)
    iapply HΨ; itrivial
  (try wp_auto)
  wp_apply Hst $$ %ci %{ cd with Values := vsv } %desc %cc %method %g %gs [] as %cs %serr #Hserr
  · iframe #
  cases serr with
  | ok se =>
    (try wp_auto)
    wp_apply wp_isContextError (GoInterface.ok se) $$ [$Hserr] as %b1 -
    cases b1
    · -- not a context error: the log
      (try wp_auto)
      wp_apply wp_zapError as %f1 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply wp_GetLogger c $$ [$Hlg] as %lg %Hlgn
      wp_apply wp_Error lg _ _ $$ []
      · iframe #; ipureintro; exact Hlgn
      (try wp_auto)
      iapply HΨ; itrivial
    · (try wp_auto)
      wp_bind (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #()))
      iapply wp_ctxOk_Err $$ Hctx'
      inext
      iintro %e
      cases e with
      | ok ei =>
        (try wp_auto)
        iapply HΨ; itrivial
      | nil =>
        (try wp_auto)
        wp_apply wp_zapError as %f1 -
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply wp_GetLogger c $$ [$Hlg] as %lg %Hlgn
        wp_apply wp_Error lg _ _ $$ []
        · iframe #; ipureintro; exact Hlgn
        (try wp_auto)
        iapply HΨ; itrivial
  | nil =>
  (try wp_auto)
  rw [recv_eq_func_mk]
  (try wp_auto)
  iapply HΨ; itrivial

/-- (etcd-io/etcd#21739) The quiet contract, proved with no spec of `zap.Logger.Error` (nor of
`zap.Error`, `GetLogger`: the log's arguments), with `withVersion`'s `spec_done`,
`isContextError`'s `spec_ctx`, and the false hypothesis `Client.getToken.spec_ctx`. -/
theorem Client.streamClientInterceptor.wp_proof_quiet
    (wp_reuse : reuseOrNewWithCallOptions.spec (GF := GF) (hG := hG))
    (wp_withVersion : withVersion.spec_done (GF := GF) (hG := hG))
    (wp_getToken : Client.getToken.spec_ctx (GF := GF) (hG := hG))
    (wp_filter : filterCallOptions.spec (GF := GF) (hG := hG))
    (wp_Errorf : status.Errorf.spec (GF := GF) (hG := hG))
    (wp_isContextError : isContextError.spec_ctx (GF := GF) (hG := hG)) :
    Client.streamClientInterceptor.spec_quiet (GF := GF) (hG := hG) := by
  intro c sl ros
  wp_start as ⟨#Hc, #Hsl, #Hros⟩
  ihave Hci : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, ⟨%dp, %dov, #Hdp, #Hdov, #Hdbf⟩⟩
  wp_auto
  ipersist c
  wp_apply_raw wp_reuse dp sl ros $$ []
  · iframe #
    unfold retryOptsAt
    iexists dov
    iframe #
    unfold optionsOk
    iexact Hdbf
  inext
  iintro %io #Hio
  wp_pures
  wp_alloc intOpts_ptr as intOpts
  wp_pures
  wp_store
  ipersist intOpts
  wp_auto
  rw [recv_eq_func_mk]
  iapply HΦ
  unfold etcdStreamInterceptorQuiet
  iintro !> %ctx %cd %desc %dv %cc %method %st %opts %vs %Ψ !>
    ⟨#Hctx, #Hdone, #Hdesc, #Hst, #Hopts, #Hok⟩ HΨ
  (try wp_auto)
  wp_apply wp_withVersion ctx cd $$ [$Hctx $Hdone] as %c' ⟨%ci, %vsv, %Hc', #Hctx', #Hdone'⟩
  subst Hc'
  (try wp_auto)
  wp_apply wp_getToken c ci { cd with Values := vsv } $$ [$Hc $Hctx' $Hdone'] as %terr ⟨#Hterr, #Htcc⟩
  cases terr with
  | ok te =>
    (try wp_auto)
    icases Htcc with (%Habs | #Hcc)
    · exact absurd Habs (by simp)
    -- a context status (`spec_ctx`) on a done context (`ctxErrDone`): no log
    wp_apply wp_isContextError (GoInterface.ok te) $$ [$Hcc]
    (try wp_auto)
    wp_bind (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #()))
    iunfold ctxErrDone at Hdone'
    iapply Hdone'
    inext
    iintro %ei
    (try wp_auto)
    iapply HΨ; itrivial
  | nil =>
  (try wp_auto)
  wp_apply wp_filter opts vs $$ [$Hopts $Hok] as %g %r ⟨%gs, %ros', Hg, Hgc, %Hgs, Hr, #Hros'⟩
  (try wp_auto)
  ipersist Hg
  ipersist Hr
  ihave #Hros'' : iprop([∗list] ro ∈ ros', optApplyOk (GF := GF) ro.applyFunc') $$ []
  · iapply (BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := ros')
      (Φ := fun _ (ro : go_etcd_io.etcd.client.v3.retryOption) => retryApplyOk (GF := GF) ro.applyFunc')
      (Ψ := fun _ ro => optApplyOk (GF := GF) ro.applyFunc')
      (fun {_ ro} => optApplyOk_of_retryApplyOk ro.applyFunc'))
    iexact Hros'
  wp_apply wp_reuse io r ros' $$ [] as %co #Hco
  · iframe #
  ihave #Hco' := Hco
  iunfold retryOptsAt at Hco'
  icases Hco' with ⟨%cov, #Hcov, #Hcovk⟩
  icases options_fields_ro co cov $$ Hcov with ⟨#Hrp, #Hmax, #Hbf, #Hra⟩
  iunfold grpcStreamerCtxErr at Hst
  ihave #Hdesc' := Hdesc
  iStructNamed Hdesc'
  (try wp_auto)
  wp_if_destruct
  · -- `callOpts.max == 0`: the streamer's stream
    (try wp_auto)
    wp_apply Hst $$ %ci %{ cd with Values := vsv } %desc %cc %method %g %gs [] as %cs %serr -
    · iframe #
    (try wp_auto)
    iapply HΨ; itrivial
  (try wp_auto)
  generalize dv.ClientStreams' = bcs
  cases bcs
  rotate_left
  · -- `desc.ClientStreams`: `Unimplemented`
    (try wp_auto)
    wp_apply wp_Errorf (W32 12) _ _ $$ [] as %e -
    · ihave #Hst' : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
      · iPkgInit
      iframe #
      ipureintro
      intro h
      have h' : (W32 12) = W32 0 := go.intoVal_inj h
      exact absurd h' (by decide)
    (try wp_auto)
    iapply HΨ; itrivial
  (try wp_auto)
  wp_apply Hst $$ %ci %{ cd with Values := vsv } %desc %cc %method %g %gs [] as %cs %serr ⟨#Hserr, #Hscc⟩
  · iframe #
  cases serr with
  | ok se =>
    (try wp_auto)
    icases Hscc with (%Habs | #Hcc)
    · exact absurd Habs (by simp)
    -- a context status (`spec_ctx`) on a done context (`ctxErrDone`): no log
    wp_apply wp_isContextError (GoInterface.ok se) $$ [$Hcc]
    (try wp_auto)
    wp_bind (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #()))
    iunfold ctxErrDone at Hdone'
    iapply Hdone'
    inext
    iintro %ei
    (try wp_auto)
    iapply HΨ; itrivial
  | nil =>
  (try wp_auto)
  rw [recv_eq_func_mk]
  (try wp_auto)
  iapply HΨ; itrivial


end proof

end EtcdGrove
end Perennial
