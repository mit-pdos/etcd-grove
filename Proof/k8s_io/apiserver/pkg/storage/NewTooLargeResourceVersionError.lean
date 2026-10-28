/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/NewTooLargeResourceVersionError.lean`. Lean-first (no
Rocq counterpart).

The message (`fmt.Sprintf`), the timeout error (`apierrors.NewTimeoutError`, whose details it
owns), the cause (the package's `tooLargeResourceVersionCauseMsg`, `storageInit`) set in its
details; a `*StatusError` as an `error` is not `nil`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewTimeoutError
public import Perennial.Proof.fmt.Link
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

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
  icases Hsg with ⟨%rw, %tl, -, #Htl⟩
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply (_root_.Perennial.fmt.wp_Sprintf _ _ _ (DFrac.own 1) (by
    exact _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 _)
      (_root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 _) _root_.Perennial.fmt.ArgsWf.nil)))
    $$ [$Hasl] as %s -
  (try wp_auto)
  wp_apply (wp_NewTimeoutError s retry) as %p ⟨%st, %dv, Hp, Hd, -⟩
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %csl ⟨Hcsl, -⟩
  iStructNamed Hp
  iStructNamed ErrStatus
  iStructNamed Hd
  (try wp_auto)
  iapply HΦ
  ipureintro
  simp

end proof

end EtcdGrove
end Perennial
