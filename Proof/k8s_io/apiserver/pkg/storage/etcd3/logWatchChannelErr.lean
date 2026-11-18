/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/logWatchChannelErr.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.logWatchChannelErr
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.isCancelError
public import Spec.strings.Contains
public import Spec.k8s_io.klog.v2.Warningf
public import Spec.k8s_io.klog.v2.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem logWatchChannelErr.wp_proof
    (wp_isCancelError : isCancelError.spec (GF := GF) (hG := hG))
    (wp_Contains : strings.Contains.spec (GF := GF) (hG := hG))
    (wp_Warningf : klog.Warningf.spec (GF := GF) (hG := hG))
    (wp_Errorf : klog.Errorf.spec (GF := GF) (hG := hG)) :
    logWatchChannelErr.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hok
  ihave #Hok' := Hok
  iunfold kErrOk at Hok'
  icases Hok' with ⟨%e, %He, -, #Hstr, %Hfmt, -⟩
  subst He
  ihave #Pstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Pkl : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
  · iPkgInit
  ihave HerrF : fmt.argOk (GF := GF) (GoInterface.ok e) $$ []
  · unfold fmt.argOk
    iright; ileft
    iframe #
    ipureintro; exact Hfmt
  rw [fmt.stringMethodSpec_unfold]
  wp_auto
  wp_bind (App (Val #(methods e.ty go!"Error" e.v)) (Val #()))
  iapply Hstr
  inext
  iintro %s
  wp_auto
  wp_apply wp_Contains
  (try wp_auto)
  by_cases hc : go!"mvcc: required revision has been compacted" <:+: s
  · simp only [hc, decide_true]
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Warningf _ _ _ _ $$ [$Hsl HerrF] as -
    · iframe #
      klog_args_intro
      isplitl [HerrF]
      · iapply klog.argOkAt_of_argOk
        isplitr
        · ipureintro; decide
        iexact HerrF
      itrivial
    (try wp_auto)
    iapply HΦ; itrivial
  · simp only [hc, decide_false]
    wp_auto
    wp_apply wp_isCancelError $$ [$Hok] as %b -
    (try wp_auto)
    cases b
    case true =>
      wp_auto
      iapply HΦ; itrivial
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Errorf _ _ _ _ $$ [$Hsl HerrF] as -
    · iframe #
      klog_args_intro
      isplitl [HerrF]
      · iapply klog.argOkAt_of_argOk
        isplitr
        · ipureintro; decide
        iexact HerrF
      itrivial
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end k8s
end EtcdGrove
end Perennial
