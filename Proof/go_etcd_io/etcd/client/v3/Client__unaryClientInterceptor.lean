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
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec errCellOk)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `▷ P` under a name. Before each step, `wp_auto` and `wp_apply` check whether a hypothesis
has a `▷` they may strip (`strippableLater`, not below a wand) and, if one has, search every
hypothesis for one (`IntoLaterN`), the invoker's specification `Hinv` taking seconds; the request's
precondition, kept until its attempt (`Hpre`, `Hp`), has its `▷` here, out of that check. -/
private def laterHid (P : IProp GF) : IProp GF := iprop(▷ P)

set_option maxHeartbeats 1600000 in
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
  icases Hci with ⟨-, ⟨%dp, %dov, #Hdp, #Hdov, #Hdbf, %Hdpol⟩, -⟩
  wp_auto
  ipersist c
  wp_apply_raw wp_reuse dp sl ros true $$ []
  · iframe Hros Hsl Hpkg
    unfold retryOptsAt
    iexists dov
    iframe Hdov
    unfold optionsOk
    iexact Hdbf
  inext
  iintro %io ⟨#Hio, %-, #Hiopol⟩
  -- (D29) the interceptor's options keep the default policy, `nonRepeatable`
  ihave #Hiop : retryOptsPol io (W8 1) $$ []
  · iapply Hiopol $$ %rfl
    unfold retryOptsPol
    iexists dov
    iframe Hdov
    ipureintro; exact Hdpol
  wp_pures
  wp_alloc intOpts_ptr as intOpts
  wp_pures
  wp_store
  ipersist intOpts
  wp_auto
  iapply HΦ
  -- (D29) both modes: any precondition persistent, or an ordinary one for a write on a
  -- refusal-free connection
  iapply etcdInterceptorOkM_split
  iintro !> %md
  unfold etcdInterceptorOkM
  iintro !> %conn %addr %ics %dopts %inv %method %Req %Rep %Spec %m %Φ' %ctx %cd %inp %out %opts
    %vs %Ψ !> ⟨#Hgc, #Hinv, #Hrpc, Hpre, #Hctx, Hsend, Hblank, #Hopts, #Hok⟩ HΨ
  -- (D29) a write's ordinary precondition, never retried (`.write`), or a persistent one (`.any`)
  obtain ⟨once, hon⟩ : ∃ b : Bool, b = (md != AttemptMode.any) := ⟨_, rfl⟩
  ihave ⟨Hpre, %Hw⟩ : iprop((if once then laterHid (Spec m Φ') else iprop(□ laterHid (Spec m Φ'))) ∗
      ⌜md = AttemptMode.write → kvMethod method ∧ (∀ a ∈ addr, noRefusalAt a) ∧ scalarOpts vs⌝) $$ [Hpre]
  · subst hon
    cases md
    · unfold modePre laterHid
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      iframe Hpre; ipureintro; intro h; cases h
    · unfold modePre laterHid
      simp only [show (AttemptMode.write != AttemptMode.any) = true from rfl, ↓reduceIte]
      icases Hpre with ⟨Hpre, %Hw⟩
      iframe Hpre; ipureintro; intro _; exact Hw
  ihave Hout := Rep.blank_own out $$ Hblank
  (try wp_auto)
  wp_apply wp_withVersion ctx cd $$ [$Hctx] as %c' ⟨%ci, %vsv, %Hc', #Hctx'⟩
  subst Hc'
  (try wp_auto)
  wp_apply wp_filter opts vs $$ [$Hopts $Hok] as %g %r ⟨%gs, %ros', Hg, Hgc, %Hgs, Hr, #Hros', %Hnone⟩
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
  ihave #Hros'' := optApplyKeep_of_retryApplyOks ros' $$ Hros'
  wp_apply wp_reuse io r ros' false $$ [] as %co ⟨#Hco, %Hco0, -⟩
  · iframe Hros'' Hr Hio
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
  -- (D29) a write's call options are scalars: its options are the interceptor's, `nonRepeatable`
  ihave %Hcovpol : ⌜md = AttemptMode.write → cov.retryPolicy' = W8 1⌝ $$ []
  · cases md
    · ipureintro; intro h; cases h
    · have Hcoio : co = io := Hco0 (Hnone (Hw rfl).2.2)
      subst Hcoio
      iunfold retryOptsPol at Hiop
      icases Hiop with ⟨%ov2, #Hov2, %Hp2⟩
      icombine Hcov Hov2 gives %Heq
      subst Heq
      ipureintro; intro _; exact Hp2
  ihave #Hcop : retryOptsPol co cov.retryPolicy' $$ []
  · unfold retryOptsPol; iexists cov; iframe Hcov; ipureintro; first | rfl | trivial
  icases options_fields_ro co cov $$ Hcov with ⟨#Hrp, #Hmax, #Hbf, #Hra⟩
  iunfold grpcInvokerOk at Hinv
  (try wp_auto)
  wp_if_destruct
  · -- `callOpts.max == 0`: one attempt
    ihave Hsp : ▷ Spec m Φ' $$ [Hpre]
    · cases once
      · simp only [Bool.false_eq_true, ↓reduceIte, laterHid]; icases Hpre with #Hpre; iexact Hpre
      · simp only [↓reduceIte, laterHid]; iexact Hpre
    wp_apply Hinv $$ %method %Req %Rep %Spec %m %Φ' %ci
        %{ cd with Values := vsv } %inp %out %g' %(gs ++ [pv]) %([p_ptr] : List Loc) [Hsend Hout Hpb Hsp]
      as %err ⟨Hsend, -, Hres⟩
    · iframe Hg' Hctx' Hrpc
      iframe
      isplitl []
      · ipureintro; exact Hopt
      iapply BigSepL.bigSepL_nil.2
      itrivial
    iapply HΨ
    iframe
    icases Hres with (⟨%He, Hm⟩ | ⟨%He, #Hse, #Hcl, -⟩)
    · ileft; iframe; ipureintro; exact He
    · iright; iframe Hcl Hse; ipureintro; exact He
  have Hmax0 := Hif
  ihave IHL : iprop(∃ (a : w64) (le : GoInterface),
      -- (D29) a write is never retried: its first attempt is its only one
      "%Hwa" ∷ ⌜md = AttemptMode.write → a = W64 0⌝ ∗
      "attempt" ∷ attempt_ptr ↦ a ∗ "lastErr" ∷ lastErr_ptr ↦ le ∗ "Hsend" ∷ Req.send inp m ∗
      "Hout" ∷ Rep.own out ∗ "Hpb" ∷ grpcPeerBuf p_ptr ∗
      "#Hle" ∷ (⌜a = W64 0⌝ ∨ (⌜le ≠ GoInterface.nil ∧ clientErr le⌝ ∗ statusErrOk le ∗ errCellOk le)) ∗
      -- (D21 M6) the request's precondition: the first attempt's if ordinary
      "Hp" ∷ (if once then iprop(⌜a = W64 0⌝ -∗ ▷ Spec m Φ') else iprop(□ laterHid (Spec m Φ'))))
    $$ [attempt lastErr Hsend Hout Hpb Hpre]
  · iexists W64 0, GoInterface.nil
    simp only [named]
    isplitr
    · ipureintro; intro _; first | rfl | trivial
    iframe
    isplitr
    · ileft; itrivial
    cases once
    · simp only [Bool.false_eq_true, ↓reduceIte] at *; iexact Hpre
    · simp only [↓reduceIte] at *; iintro -; unfold laterHid; iexact Hpre
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
      icases Hwerr with ⟨%Hce, #Hse, #Hcl⟩
      iframe Hcl Hse
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
      · ipureintro; exact Hlgn
      -- the attempt: (D29) with an ordinary precondition (a write), the first and only one
      have Hlt1 : once = true → a = W64 0 := fun h => by
        subst hon
        cases md with
        | any => exact absurd h (by decide)
        | write => exact Hwa rfl
      ihave ⟨Hsp, Hp⟩ : iprop(▷ Spec m Φ' ∗
          (if once then iprop(⌜a + W64 1 = W64 0⌝ -∗ ▷ Spec m Φ') else iprop(□ laterHid (Spec m Φ'))))
          $$ [Hp]
      · cases once
        · simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hp with #Hp
          unfold laterHid
          iframe Hp
        · simp only [↓reduceIte]
          have Ha0 := Hlt1 rfl
          isplitl [Hp]
          · iapply Hp; ipureintro; exact Ha0
          · iintro %h; exfalso; rw [Ha0] at h; revert h; decide
      wp_apply Hinv $$ %method %Req %Rep %Spec %m %Φ' %ci
          %{ cd with Values := vsv } %inp %out %g' %(gs ++ [pv]) %([p_ptr] : List Loc) [Hsend Hout Hpb Hsp]
        as %err ⟨Hsend, Hpbs, Hres⟩
      · iframe Hg' Hctx' Hrpc
        iframe
        isplitl []
        · ipureintro; exact Hopt
        iapply BigSepL.bigSepL_nil.2
        itrivial
      icases Hpbs with ⟨Hpb, -⟩
      icases Hres with (⟨%He, Hm⟩ | ⟨%He, #Hse, #Hcl, Hout, %Hnr⟩)
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
      · ipureintro; exact Hlgn2
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
            iframe Hcl Hse
            ipureintro; exact ⟨Hne, Hce⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists a + W64 1, GoInterface.ok ei
          simp only [named]
          isplitr
          · -- (D29) a write's policy is `nonRepeatable`, which returned above
            ipureintro; intro hw; exfalso
            have := Hcovpol hw
            simp_all
          iframe
          iright
          iframe Hcl Hse
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
          iframe Hcl Hse
          ipureintro; exact ⟨Hne, Hce⟩
        | nil =>
          (try wp_auto)
          wp_if_destruct
          · -- a non-repeatable call: its attempt's error (8a24be2a3)
            wp_for_post
            iapply HΨ
            iframe
            iright
            iframe Hcl Hse
            ipureintro; exact ⟨Hne, Hce⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists a + W64 1, GoInterface.ok ei
          simp only [named]
          isplitr
          · -- (D29) a write's policy is `nonRepeatable`, which returned above
            ipureintro; intro hw; exfalso
            have := Hcovpol hw
            simp_all
          iframe
          iright
          iframe Hcl Hse
          ipureintro; exact ⟨Hne, Hce⟩
      (try wp_auto)
      wp_apply wp_shouldRefresh c (GoInterface.ok ei) co $$ [$Hc $Hco $Hse] as %b2 %Hb2
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
          · ipureintro; exact Hlgn3
          wp_for_post
          iapply HΨ
          iframe
          iright
          iunfold clientErrOk at Hgt
          icases Hgt with ⟨%Hgce, #Hgse, #Hgcl⟩
          iframe Hgcl Hgse
          ipureintro; exact ⟨by simp, Hgce (by simp)⟩
        | nil =>
          (try wp_auto)
          wp_for_post
          iframe
          iexists a + W64 1, GoInterface.ok ei
          simp only [named]
          isplitr
          · -- (D29) a refresh follows an auth refusal, which a refusal-free connection never sends
            ipureintro; intro hw; exfalso
            rcases Hnr ⟨(Hw hw).1, (Hw hw).2.1⟩ with h | h
            · exact Hne h
            · exact h (Hb2 rfl)
          iframe
          iright
          iframe Hcl Hse
          ipureintro; exact ⟨Hne, Hce⟩
      (try wp_auto)
      wp_apply wp_isSafeRetry c (GoInterface.ok ei) co cov.retryPolicy' $$ [$Hc $Hco $Hse $Hcop] as %b3 %Hb3
      · ipureintro; exact ⟨Hne, Hce⟩
      cases b3
      · (try wp_auto)
        wp_for_post
        iapply HΨ
        iframe
        iright
        iframe Hcl Hse
        ipureintro; exact ⟨Hne, Hce⟩
      · (try wp_auto)
        wp_for_post
        iframe
        iexists a + W64 1, GoInterface.ok ei
        simp only [named]
        isplitr
        · -- (D29) a write is retried only after a refusal
          ipureintro; intro hw; exfalso
          rcases Hb3 rfl with h | h
          · rcases Hnr ⟨(Hw hw).1, (Hw hw).2.1⟩ with h' | h'
            · exact Hne h'
            · exact h' h
          · rw [Hcovpol hw] at h; simp at h
        iframe
        iright
        iframe Hcl Hse
        ipureintro; exact ⟨Hne, Hce⟩
  · iapply HΨ
    iframe
    iright
    icases Hle with (%Ha | ⟨%Hl, #Hls, #Hlcl⟩)
    · exfalso
      subst Ha
      apply Hif
      have h1 : uint.Z cov.max' ≠ 0 := fun h => Hmax0 (by word)
      word
    · iframe Hlcl Hls; ipureintro; exact Hl

end proof

end EtcdGrove
end Perennial
