/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__dialSetupOpts.lean` (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__dialSetupOpts
public import Spec.go_etcd_io.etcd.client.v3.Client__roundRobinQuorumBackoff
public import Spec.go_etcd_io.etcd.client.v3.Client__streamClientInterceptor
public import Spec.go_etcd_io.etcd.client.v3.Client__unaryClientInterceptor
public import Spec.go_etcd_io.etcd.client.v3.withBackoff
public import Spec.go_etcd_io.etcd.client.v3.withMax
public import Spec.google_golang_org.grpc.WithTransportCredentials
public import Spec.google_golang_org.grpc.WithKeepaliveParams
public import Spec.google_golang_org.grpc.WithStreamInterceptor
public import Spec.google_golang_org.grpc.WithUnaryInterceptor
public import Spec.google_golang_org.grpc.credentials.insecure.NewCredentials

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.dialSetupOpts.wp_proof
    (wp_rrBackoff : Client.roundRobinQuorumBackoff.spec (GF := GF) (hG := hG))
    (wp_withBackoff : withBackoff.spec (GF := GF) (hG := hG))
    (wp_withMax : withMax.spec (GF := GF) (hG := hG))
    (wp_streamIc : Client.streamClientInterceptor.spec (GF := GF) (hG := hG))
    (wp_unaryIc : Client.unaryClientInterceptor.spec (GF := GF) (hG := hG))
    (wp_NewCredentials : insecure.NewCredentials.spec (GF := GF) (hG := hG))
    (wp_WithKeepaliveParams : grpc.WithKeepaliveParams.spec (GF := GF) (hG := hG))
    (wp_WithTransportCredentials : grpc.WithTransportCredentials.spec (GF := GF) (hG := hG))
    (wp_WithStreamInterceptor : grpc.WithStreamInterceptor.spec (GF := GF) (hG := hG))
    (wp_WithUnaryInterceptor : grpc.WithUnaryInterceptor.spec (GF := GF) (hG := hG)) :
    Client.dialSetupOpts.spec (GF := GF) (hG := hG) := by
  intro c cfg cr sl ds
  wp_start as ⟨#Hc, #Hcfg, #Hds⟩
  ihave #Hvars : (clientNewVars : IProp GF) $$ []
  · iapply clientNewVars_of_init; iPkgInit
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  ihave #Hins : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.credentials.insecure $$ []
  · iPkgInit
  iunfold clientNewVars at Hvars
  icases Hvars with ⟨-, ⟨%n0, #Hn0⟩, ⟨%w0, #Hw0⟩, ⟨%j0, #Hj0⟩⟩
  iunfold dialOptsAt at Hds
  icases Hds with ⟨%os, #Hos, %Hosds⟩
  iStructNamed Hcfg
  wp_auto
  ihave Hnil := ownSlice_nil (V := GoInterface) (GF := GF) (DFrac.own 1)
  ihave Hnilc := ownSliceCap_nil (V := GoInterface) (GF := GF)
  -- (2026-10-21, D28) grpc's keepalive option first, if `DialKeepAliveTime` is positive
  wp_join iprop(c_ptr ↦ c ∗ ∃ (o0 : GoSlice) (ka : List GoInterface), opts_ptr ↦ o0 ∗
      o0 ↦* ka ∗ ownSliceCap GoInterface o0 (DFrac.own 1) ∗
      ⌜List.Forall₂ grpcDialOptIs ka (kaOpts cfg)⌝) at next
      with [c opts Hnil Hnilc] as ⟨c, %o0, %ka, opts, Ho0, Ho0c, %Hka⟩
  · wp_if_destruct
    · (try wp_auto)
      wp_apply wp_WithKeepaliveParams _ $$ [$Hgrpc] as %kv %Hkv
      wp_apply wp_slice_literal (V := GoInterface) [kv]
      isplitr
      · ipureintro; rfl
      iintro %lp ⟨Hl, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      rw [show (zero_val GoSlice) = slice.nil from rfl]
      wp_apply (wp_slice_append (V := GoInterface) slice.nil [] _ [kv] (DFrac.own 1))
        $$ [$Hnil $Hnilc $Hl] as %ok ⟨Hok, Hokc, -⟩
      wp_join_done
      iframe c
      iexists ok, [kv]
      iframe
      ipureintro
      unfold kaOpts
      have hpos : 0 < sint.Z cfg.DialKeepAliveTime' := by
        have h0 : sint.Z (W64 0) = 0 := by decide
        word
      simp only [hpos, ↓reduceIte]
      exact .cons Hkv .nil
    · wp_join_done
      iframe c
      iexists slice.nil, []
      iframe opts Hnil Hnilc
      ipureintro
      unfold kaOpts
      have hneg : ¬ 0 < sint.Z cfg.DialKeepAliveTime' := by
        have h0 : sint.Z (W64 0) = 0 := by decide
        word
      simp only [hneg, ↓reduceIte]
      exact .nil
  wp_apply wp_slice_append_dfrac (V := GoInterface) o0 ka (DFrac.own 1) sl os DFrac.discard
    $$ [$Ho0 $Ho0c $Hos] as %o1 ⟨Ho1, Ho1c, -⟩
  · ipureintro; exact DFrac.valid_own_one
  wp_join iprop(∃ (o2 : GoSlice) (v : GoInterface), opts_ptr ↦ o2 ∗ o2 ↦* (ka ++ os ++ [v]) ∗
      ownSliceCap GoInterface o2 (DFrac.own 1) ∗ ⌜grpcDialOptIs v .transportCreds⌝) at next
      with [opts Ho1 Ho1c creds] as ⟨%o2, %v, opts, Ho2, Ho2c, %Hv⟩
  · cases cr with
    | nil =>
      wp_auto
      wp_apply wp_NewCredentials $$ [$Hins] as %ic -
      wp_apply wp_WithTransportCredentials ic $$ [$Hgrpc] as %v %Hv
      wp_apply wp_slice_literal (V := GoInterface) [v]
      isplitr
      · ipureintro; rfl
      iintro %lp ⟨Hl, -⟩
      wp_apply wp_slice_append $$ [$Ho1 $Ho1c $Hl] as %o2 ⟨Ho2, Ho2c, -⟩
      wp_join_done
      iexists o2, v
      iframe
      ipureintro; exact Hv
    | ok cri =>
      wp_auto
      wp_apply wp_WithTransportCredentials (GoInterface.ok cri) $$ [$Hgrpc] as %v %Hv
      wp_apply wp_slice_literal (V := GoInterface) [v]
      isplitr
      · ipureintro; rfl
      iintro %lp ⟨Hl, -⟩
      wp_apply wp_slice_append $$ [$Ho1 $Ho1c $Hl] as %o2 ⟨Ho2, Ho2c, -⟩
      wp_join_done
      iexists o2, v
      iframe
      ipureintro; exact Hv
  wp_join iprop(c_ptr ↦ c ∗ ∃ n : w64, unaryMaxRetries_ptr ↦ n ∗
      ⌜cfg.MaxUnaryRetries' = W64 1 → n = W64 1⌝) with [c unaryMaxRetries]
    as ⟨c, %nr, unaryMaxRetries, %Hnr⟩
  all_goals try (first
    | (iframe; ipureintro; intro h; exact h)
    | (iframe; ipureintro; intro h; exfalso; rw [h] at Hif; exact Hif (by decide)))
  wp_join iprop(c_ptr ↦ c ∗ ∃ d : time.Duration, backoffWaitBetween_ptr ↦ d)
    with [c backoffWaitBetween] as ⟨c, %wb, backoffWaitBetween⟩
  all_goals try (iframe; iexists _; iframe)
  wp_join iprop(c_ptr ↦ c ∗ ∃ j : w64, backoffJitterFraction_ptr ↦ j) at next
    with [c backoffJitterFraction] as ⟨c, %jf, backoffJitterFraction⟩
  · generalize (float64Leb (W64 0) cfg.BackoffJitterFraction' &&
      !decide (cfg.BackoffJitterFraction' = W64 0)) = b
    cases b
    all_goals wp_auto
    all_goals wp_join_done
    all_goals (iframe; iexists _; iframe)
  wp_apply wp_rrBackoff c wb jf $$ [$Hc] as %bf #Hbf
  wp_apply wp_withBackoff bf $$ [$Hbf] as %rro #Hrro'
  ihave #Hrro := optApplyMax_ok _ _ $$ Hrro'
  wp_apply wp_withMax (W64 0) as %m0 #Hm0'
  ihave #Hm0 := optApplyMax_ok _ _ $$ Hm0'
  wp_apply wp_slice_literal (V := go_etcd_io.etcd.client.v3.retryOption) [m0, rro]
  isplitr
  · ipureintro; rfl
  iintro %l1 ⟨Hl1, -⟩
  ipersist Hl1
  (try wp_auto)
  ihave #Hros1 : iprop([∗list] ro ∈ [m0, rro], optApplyOk (GF := GF) ro.applyFunc') $$ []
  · iapply BigSepL.bigSepL_cons.2; iframe Hm0
    iapply BigSepL.bigSepL_cons.2; iframe Hrro
    iapply BigSepL.bigSepL_nil.2; itrivial
  wp_apply wp_streamIc c _ [m0, rro] $$ [$Hc $Hl1 $Hros1] as %si %Hsi
  wp_apply wp_WithStreamInterceptor si $$ [$Hgrpc] as %o3 %Ho3
  wp_apply wp_withMax nr as %m1 #Hm1
  wp_apply wp_slice_literal (V := go_etcd_io.etcd.client.v3.retryOption) [m1, rro]
  isplitr
  · ipureintro; rfl
  iintro %l2 ⟨Hl2, -⟩
  ipersist Hl2
  (try wp_auto)
  ihave #Hros2 : iprop([∗list] ro;k ∈ [m1, rro];[some nr, none], optApplyMax (GF := GF) ro.applyFunc' k) $$ []
  · iapply BigSepL2.bigSepL2_cons.2; iframe Hm1
    iapply BigSepL2.bigSepL2_cons.2; iframe Hrro'
    iapply BigSepL2.bigSepL2_nil.2; itrivial
  wp_apply wp_unaryIc c _ [m1, rro] [some nr, none] $$ [$Hc $Hl2 $Hros2] as %ic ⟨#Hic, #Hic1⟩
  wp_apply wp_WithUnaryInterceptor ic $$ [$Hgrpc] as %o4 %Ho4
  wp_apply wp_slice_literal (V := GoInterface) [o3, o4]
  isplitr
  · ipureintro; rfl
  iintro %l3 ⟨Hl3, -⟩
  (try wp_auto)
  iapply wp_fupd
  wp_apply wp_slice_append $$ [$Ho2 $Ho2c $Hl3] as %o5 ⟨Ho5, Ho5c, -⟩
  ipersist Ho5
  imodintro
  iapply HΦ
  iexists si, ic
  iframe Ho5c Hic
  isplitr
  · iunfold dialOptsAt
    iexists _
    iframe Ho5
    ipureintro
    simp only [List.append_assoc, List.cons_append]
    exact List.Forall₂.append Hka (List.Forall₂.append Hosds (.cons Hv (.cons Ho3 (.cons Ho4 .nil))))
  isplitr
  · ipureintro; exact Hsi
  iintro %Hm
  iapply Hic1
  ipureintro
  intro mx
  rw [show maxAfter mx [some nr, none] = nr from rfl, Hnr Hm]
  decide

end proof

end EtcdGrove
end Perennial
