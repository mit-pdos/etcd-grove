/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__unaryClientInterceptor.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__unaryClientInterceptor
public import Spec.go_etcd_io.etcd.client.v3.reuseOrNewWithCallOptions
public import Spec.go_etcd_io.etcd.client.v3.withVersion
public import Spec.go_etcd_io.etcd.client.v3.filterCallOptions
public import Spec.google_golang_org.grpc.Peer
public import Spec.go_etcd_io.etcd.client.v3.waitRetryBackoff
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger
public import Spec.google_golang_org.grpc.ClientConn__Target
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Uint
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.google_golang_org.grpc.peer.Peer__String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_etcd_io.etcd.client.v3.isContextError
public import Spec.go_etcd_io.etcd.client.v3.Client__shouldRefreshToken
public import Spec.go_etcd_io.etcd.client.v3.Client__refreshToken
public import Spec.go_etcd_io.etcd.client.v3.isSafeRetry

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

theorem Client.unaryClientInterceptor.wp_proof
    (wp_reuse : reuseOrNewWithCallOptions.spec (GF := GF) (hG := hG))
    (wp_withVersion : withVersion.spec (GF := GF) (hG := hG))
    (wp_filter : filterCallOptions.spec (GF := GF) (hG := hG))
    (wp_Peer : grpc.Peer.spec (GF := GF) (hG := hG))
    (wp_wait : waitRetryBackoff.spec (GF := GF) (hG := hG))
    (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG))
    (wp_Target : grpc.ClientConn.Target.spec (GF := GF) (hG := hG))
    (wp_zapString : zap.String.spec (GF := GF) (hG := hG))
    (wp_zapUint : zap.Uint.spec (GF := GF) (hG := hG))
    (wp_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (wp_PeerString : peer.Peer.String.spec (GF := GF) (hG := hG))
    (wp_zapError : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_isContextError : isContextError.spec (GF := GF) (hG := hG))
    (wp_shouldRefresh : Client.shouldRefreshToken.spec (GF := GF) (hG := hG))
    (wp_refresh : Client.refreshToken.spec (GF := GF) (hG := hG))
    (wp_isSafeRetry : isSafeRetry.spec (GF := GF) (hG := hG)) :
    Client.unaryClientInterceptor.spec (GF := GF) (hG := hG) := by
  intro c sl ros
  wp_start as ⟨#Hc, #Hsl, #Hros⟩
  ihave Hci : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, ⟨%dp, %dov, #Hdp, #Hdov, #Hdbf⟩, -⟩
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
  unfold etcdInterceptorOk
  iintro !> %conn %addr %ics %dopts %inv %method %Req %Rep %Spec %m %Φ' %ctx %cd %inp %out %opts
    %vs %Ψ !> ⟨#Hgc, #Hinv, #Hrpc, #Hpre, #Hctx, Hsend, Hblank, #Hopts, #Hok⟩ HΨ
  ihave Hout := Rep.blank_own out $$ Hblank
  (try wp_auto)
  wp_apply wp_withVersion ctx cd $$ [$Hctx] as %c' ⟨%ci, %vsv, %Hc', #Hctx'⟩
  subst Hc'
  (try wp_auto)
  wp_apply wp_filter opts vs $$ [$Hopts $Hok] as %g %r ⟨%gs, %ros', Hg, Hgc, %Hgs, Hr, #Hros'⟩
  (try wp_auto)
  wp_apply wp_Peer p_ptr as %pv %Hpv
  wp_apply wp_slice_literal (V := GoInterface) [pv]
  isplitr
  · ipureintro; rfl
  iintro %lp ⟨Hl, -⟩
  wp_apply wp_slice_append $$ [$Hg $Hgc $Hl] as %g' ⟨Hg', -, -⟩
  (try wp_auto)
  ipersist Hg'
  ipersist Hr
  ihave #Hros'' : iprop([∗list] ro ∈ ros', optApplyOk (GF := GF) ro.applyFunc') $$ []
  · iapply (BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := ros')
      (Φ := fun _ (ro : go_etcd_io.etcd.client.v3.retryOption) => retryApplyOk (GF := GF) ro.applyFunc')
      (Ψ := fun _ ro => optApplyOk (GF := GF) ro.applyFunc')
      (fun {_ ro} => optApplyOk_of_retryApplyOk ro.applyFunc'))
    iexact Hros'
  wp_apply wp_reuse io r ros' $$ [] as %co #Hco
  · iframe #
  have Hopt : ∀ w ∈ gs ++ [pv], grpcOptOk [p_ptr] w := by
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact Or.inl (Hgs w hw)
    · simp only [List.mem_singleton] at hw
      subst hw
      exact Or.inr ⟨p_ptr, by simp, Hpv⟩
  ihave Hpb := grpcPeerBuf_zero p_ptr $$ p
  ihave #Hco' := Hco
  iunfold retryOptsAt at Hco'
  icases Hco' with ⟨%cov, #Hcov, #Hcovk⟩
  icases options_fields_ro co cov $$ Hcov with ⟨#Hrp, #Hmax, #Hbf, #Hra⟩
  iunfold grpcInvokerOk at Hinv
  (try wp_auto)
  wp_if_destruct
  · -- `callOpts.max == 0`: one attempt
    wp_apply Hinv $$ %method %Req %Rep %Spec %m %Φ' %ci
        %{ cd with Values := vsv } %inp %out %g' %(gs ++ [pv]) %([p_ptr] : List Loc) [Hsend Hout Hpb]
      as %err ⟨Hsend, -, Hres⟩
    · iframe #
      iframe
      isplitl []
      · ipureintro; exact Hopt
      iapply BigSepL.bigSepL_nil.2
      itrivial
    iapply HΨ
    iframe
    icases Hres with (⟨%He, Hm⟩ | ⟨%He, #Hse, -⟩)
    · ileft; iframe; ipureintro; exact He
    · iright; iframe #; ipureintro; exact He
  have Hmax0 := Hif
  ihave IHL : iprop(∃ (a : w64) (le : GoInterface),
      "attempt" ∷ attempt_ptr ↦ a ∗ "lastErr" ∷ lastErr_ptr ↦ le ∗ "Hsend" ∷ Req.send inp m ∗
      "Hout" ∷ Rep.own out ∗ "Hpb" ∷ grpcPeerBuf p_ptr ∗
      "#Hle" ∷ (⌜a = W64 0⌝ ∨ (⌜le ≠ GoInterface.nil ∧ clientErr le⌝ ∗ statusErrOk le)))
    $$ [attempt lastErr Hsend Hout Hpb]
  · iexists W64 0, GoInterface.nil
    simp only [named]
    iframe
    ileft; itrivial
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold retryClientOk at Hc'
  icases Hc' with ⟨%Hcn, #Hlg, -⟩
  wp_for IHL
  wp_if_destruct
  · wp_apply wp_wait ci { cd with Values := vsv } a co $$ [$Hctx' $Hco] as %werr #Hwerr
    cases werr with
    | ok we =>
      (try wp_auto)
      wp_for_post
      iapply HΨ
      iframe
      iright
      iunfold clientErrOk at Hwerr
      icases Hwerr with ⟨%Hce, #Hse⟩
      iframe #
      ipureintro; exact ⟨by simp, Hce (by simp)⟩
    | nil =>
      (try wp_auto)
      -- the debug log
      wp_apply wp_Target conn addr ics dopts $$ [$Hgc] as %ts -
      wp_apply wp_zapString as %f1 -
      wp_apply wp_zapString as %f2 -
      wp_apply wp_zapUint as %f3 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply wp_GetLogger c $$ [$Hlg] as %lg %Hlgn
      wp_apply wp_Debug lg _ _ $$ []
      · iframe #; ipureintro; exact Hlgn
      -- the attempt
      wp_apply Hinv $$ %method %Req %Rep %Spec %m %Φ' %ci
          %{ cd with Values := vsv } %inp %out %g' %(gs ++ [pv]) %([p_ptr] : List Loc) [Hsend Hout Hpb]
        as %err ⟨Hsend, Hpbs, Hres⟩
      · iframe #
        iframe
        isplitl []
        · ipureintro; exact Hopt
        iapply BigSepL.bigSepL_nil.2
        itrivial
      icases Hpbs with ⟨Hpb, -⟩
      icases Hres with (⟨%He, Hm⟩ | ⟨%He, #Hse, Hout⟩)
      · subst He
        (try wp_auto)
        wp_for_post
        iapply HΨ
        iframe
        ileft; iframe; ipureintro; rfl
      obtain ⟨Hne, Hce⟩ := He
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
      (try wp_auto)
      -- the warning
      wp_apply wp_Target conn addr ics dopts $$ [$Hgc] as %ts2 -
      wp_apply wp_zapString as %g1 -
      wp_apply wp_PeerString p_ptr $$ [$Hpb] as %pstr Hpb
      wp_apply wp_zapString as %g2 -
      wp_apply wp_zapString as %g3 -
      wp_apply wp_zapUint as %g4 -
      wp_apply wp_zapError as %g5 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [g1, g2, g3, g4, g5]
      isplitr
      · ipureintro; rfl
      iintro %fsl2 ⟨-, -⟩
      (try wp_auto)
      wp_apply wp_GetLogger c $$ [$Hlg] as %lg2 %Hlgn2
      wp_apply wp_Warn lg2 _ _ $$ []
      · iframe #; ipureintro; exact Hlgn2
      wp_apply wp_isContextError (GoInterface.ok ei) $$ [$Hse] as %b1 -
      cases b1
      rotate_left
      · -- a context error: the caller's context's, or retried
        ihave #HC := Hctx'
        iunfold ctxOk at HC
        icases HC with (#HC | #HQ)
        rotate_left
        · -- a quiet context (`context.TODO()`, the vertical slice's unit V2): `Err()` is `nil`
          (try wp_auto)
          iunfold ctxQuiet at HQ
          wp_bind (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #()))
          iapply HQ
          inext
          (try wp_auto)
          wp_if_destruct
          · -- a non-repeatable call: its attempt's error (8a24be2a3)
            wp_for_post
            iapply HΨ
            iframe
            iright
            iframe #
            ipureintro; exact ⟨Hne, Hce⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists a + W64 1, GoInterface.ok ei
          simp only [named]
          iframe
          iright
          iframe #
          ipureintro; exact ⟨Hne, Hce⟩
        iunfold _root_.Perennial.context.isContext at HC
        iunfold _root_.Perennial.context.isContextDef at HC
        iNamed HC
        (try wp_auto)
        wp_apply HErr $$ %Broadcast.Pending as %ce Hce'
        cases ce with
        | ok cei =>
          (try wp_auto)
          wp_for_post
          iapply HΨ
          iframe
          iright
          iframe #
          ipureintro; exact ⟨Hne, Hce⟩
        | nil =>
          (try wp_auto)
          wp_if_destruct
          · -- a non-repeatable call: its attempt's error (8a24be2a3)
            wp_for_post
            iapply HΨ
            iframe
            iright
            iframe #
            ipureintro; exact ⟨Hne, Hce⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists a + W64 1, GoInterface.ok ei
          simp only [named]
          iframe
          iright
          iframe #
          ipureintro; exact ⟨Hne, Hce⟩
      (try wp_auto)
      wp_apply wp_shouldRefresh c (GoInterface.ok ei) co $$ [$Hc $Hco $Hse] as %b2 -
      · ipureintro; exact ⟨Hne, Hce⟩
      cases b2
      rotate_left
      · -- refresh the token
        (try wp_auto)
        wp_apply wp_refresh c ci { cd with Values := vsv } $$ [$Hc $Hctx'] as %gt #Hgt
        cases gt with
        | ok gti =>
          (try wp_auto)
          wp_apply wp_Target conn addr ics dopts $$ [$Hgc] as %ts3 -
          wp_apply wp_zapString as %h1 -
          wp_apply wp_zapError as %h2 -
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [h1, h2]
          isplitr
          · ipureintro; rfl
          iintro %fsl3 ⟨-, -⟩
          (try wp_auto)
          wp_apply wp_GetLogger c $$ [$Hlg] as %lg3 %Hlgn3
          wp_apply wp_Warn lg3 _ _ $$ []
          · iframe #; ipureintro; exact Hlgn3
          wp_for_post
          iapply HΨ
          iframe
          iright
          iunfold clientErrOk at Hgt
          icases Hgt with ⟨%Hgce, #Hgse⟩
          iframe #
          ipureintro; exact ⟨by simp, Hgce (by simp)⟩
        | nil =>
          (try wp_auto)
          wp_for_post
          iframe
          iexists a + W64 1, GoInterface.ok ei
          simp only [named]
          iframe
          iright
          iframe #
          ipureintro; exact ⟨Hne, Hce⟩
      (try wp_auto)
      wp_apply wp_isSafeRetry c (GoInterface.ok ei) co $$ [$Hc $Hco $Hse] as %b3 -
      · ipureintro; exact ⟨Hne, Hce⟩
      cases b3
      · (try wp_auto)
        wp_for_post
        iapply HΨ
        iframe
        iright
        iframe #
        ipureintro; exact ⟨Hne, Hce⟩
      · (try wp_auto)
        wp_for_post
        iframe
        iexists a + W64 1, GoInterface.ok ei
        simp only [named]
        iframe
        iright
        iframe #
        ipureintro; exact ⟨Hne, Hce⟩
  · iapply HΨ
    iframe
    iright
    icases Hle with (%Ha | ⟨%Hl, #Hls⟩)
    · exfalso
      subst Ha
      apply Hif
      have h1 : uint.Z cov.max' ≠ 0 := fun h => Hmax0 (by word)
      word
    · iframe #; ipureintro; exact Hl

end proof

end EtcdGrove
end Perennial
