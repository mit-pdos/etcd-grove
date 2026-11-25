/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/NewTooLargeResourceVersionError.lean`. Lean-first (no
Rocq counterpart).

The message (`fmt.Sprintf`), the timeout error (`apierrors.NewTimeoutError`, whose details it
owns), the cause (the package's `tooLargeResourceVersionCauseMsg`, `storageInit`) set in its
details; the `*StatusError`, as an `error`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewTimeoutError
public import Perennial.Proof.fmt.Link
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.fmt.SprintfPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.NewTooLargeResourceVersionError.wp_proof
    (wp_NewTimeoutError : apierrors.NewTimeoutError.spec (GF := GF) (hG := hG)) :
    storage.NewTooLargeResourceVersionError.spec (GF := GF) (hG := hG) := by
  intro minRV curRV retry
  wp_start
  ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Pe : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  ihave #Hsg : (k8s_io.apiserver.pkg.storage.etcd3.storageInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsg with ⟨%rw, %tl, %_, -, #Htl, -, -⟩
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply (fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"Too large resource version: %d, current: %d"
    [.lit go!"Too large resource version: ", .dir none _root_.Perennial.fmt.verb_d, .lit go!", current: ", .dir none _root_.Perennial.fmt.verb_d]
    _ _ _ _ (by fmt_encode) ?fits ?pa)
    $$ [$Hasl] as %s -
  case pa =>
    rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
    simp only [List.set_cons_succ, List.set_cons_zero]
    exact .int _ _ _ _ (.uint64 _) (.int _ _ _ _ (.uint64 _) .nil)
  case fits => fmt_fits
  (try wp_auto)
  wp_apply (wp_NewTimeoutError s retry) as %p ⟨%st, %dv, Hp, Hd, %_, %hst, %hr⟩
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %csl ⟨Hcsl, -⟩
  iapply wp_fupd
  wp_auto
  ipersist Hp
  ipersist Hd
  ipersist Hcsl
  imodintro
  iapply HΦ
  unfold apierrors.tooLargeErrIs apierrors.apiErrAt apierrors.statusDetailsAt
  isplitr
  · iintro %hr0
    iexists st, _
    isplitl
    · iexists p
      isplitr
      · ipureintro; rfl
      iframe Hp
      iright
      iexists _
      iframe Hd
      iexact Hcsl
    isplitr
    · ipureintro
      exact ⟨hst.2.1, by simp⟩
    iexists _
    iframe Hd
    ipureintro
    subst hr0
    exact ⟨hst.2.2, hr⟩
  · iexists p, st, _
    iframe Hp Hd
    ipureintro; exact ⟨rfl, hst.1, hst.2.1, hst.2.2, hr⟩

end proof

end EtcdGrove
end Perennial
