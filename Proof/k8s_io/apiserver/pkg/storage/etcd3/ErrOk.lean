/-
Lean-first (no Rocq counterpart).

# The producers' errors are ones the watcher's error paths accept (`kErrOk`; k8s 7f-5a-P step 5)

Each error `startWatching` and `syncPaginated` hand to `sendError` (`notes/k8s-7f5a-draft.md` §11):

- `kErrOk_errorString`: an `*errors.errorString` whose `Error()` returns (`fmt.ErrorfPlain`'s, E3:
  `parseEvent`'s, `syncPaginated`'s and `GetCurrentResourceVersion`'s own; a context's
  `Canceled`). Over `errors.AsLeaf` (an existing trust-boundary spec).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs
public import Spec.errors.AsLeaf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section errs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- The target of `interpretWatchError`'s `errors.As` is an error type (`*corruptObjectDeletedError`
has `Error() string`). -/
theorem corrupt_asTarget :
    _root_.Perennial.errors.AsTarget (go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty) := by
  right
  go_type_set

/-- **An `errors.New`/`fmt.ErrorfPlain` error is one the watcher's error paths accept.** -/
theorem kErrOk_errorString (wp_AsLeaf : errors.AsLeaf.spec (GF := GF) (hG := hG)) (x : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢
    fmt.stringMethodSpec (GF := GF) ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
      go!"Error" -∗
    kErrOk (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  iintro #Perr #Hs
  unfold kErrOk
  iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  imodintro
  isplitr
  · ipureintro
    refine ⟨fun _ => ⟨x, rfl⟩, fun h => ?_⟩
    exfalso
    revert h
    unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
    simp
  isplitr
  · iexact Hs
  isplitr
  · ipureintro
    have := go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Format"
    simpa [go.methodSetLookup_cons, go.methodSetLookup_nil] using this
  isplitr
  · iintro %h
    exfalso
    revert h
    go_type_set
    simp
  isplitr
  · iintro %h
    exfalso
    revert h
    go_type_set
    simp
  isplitr
  · iintro %l %v %Φ Hl HΦ
    have hleaf : _root_.Perennial.errors.isLeafError
        ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ := by
      have h1 := go.MethodSetIs.method_set_is
        (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"As"
      have h2 := go.MethodSetIs.method_set_is
        (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Unwrap"
      simp only [go.methodSetLookup_cons, go.methodSetLookup_nil] at h1 h2
      refine ⟨?_, ?_, ?_⟩ <;> simp_all
    have hts : go.typeSetContains (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
        (go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty) =
          false := by
      simp only [go.typeSetContains, go.is_underlying]
      unfold k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty
        _root_.Perennial.errors.errorString.ty
      simp
    wp_apply (wp_AsLeaf x l v corrupt_asTarget hleaf hts) $$ [Hl]
    · iframe
    iintro Hl
    iapply HΦ $$ Hl
  · iintro %h
    exfalso
    revert h
    go_type_set
    simp

end errs

end k8s
end EtcdGrove
end Perennial
