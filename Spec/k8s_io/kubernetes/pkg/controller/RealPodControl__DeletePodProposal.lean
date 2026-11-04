/-
**A proposal** (the DaemonSet autoverify run, track B, 2026-11-04; review 1's M1): what
`syncNodes` needs of `RealPodControl.DeletePod`'s error and of `apierrors.IsNotFound`, stated as
candidate boundary specs for Stage 4. Not used by any proof yet; nothing rests on it.

`syncNodes`' delete goroutine (`daemon_controller.go:1129-1141`) calls `DeletePod`, and on an
error `apierrors.IsNotFound(err)`; unless it holds, it sends the error on the channel that
`NewAggregate` collects, and `HandleError`s it. So it needs: (1) `IsNotFound` returns on every error
`DeletePod` can return, (2) the error formats (`fmt.argOk`). `DeletePod`
(`controller_utils.go`) returns the client's error when `IsNotFound` holds of it, else
`fmt.Errorf("unable to delete pods: %v", err)`, whose result has no `%w`: an `errors.New`
`*errorString` (Go's `fmt.Errorf` without `%w`).

* `plainErr err`: such an error. Today's `fmt.Errorf.spec` does not say it (its result is some
  error with an `Error()` spec): the `DeletePod` proof would need `fmt.Errorf`'s spec to give the
  type when the format has no `%w` (a Perennial change, `notes/perennial-changes.md`).
* `IsNotFound.proposedSpec`: on `nil`, on a model API error (`errIs`) and on a `plainErr`,
  `IsNotFound` returns whether it is the API's `NotFound` (`errors.As` finds the `*StatusError`
  itself, or nothing: an `*errorString` has no `Unwrap`). Stated for these shapes only (review 1's
  M4: on an arbitrary error `errors.As` calls the error's methods).
* `RealPodControl.DeletePod.proposedSpec`: today's spec plus the error's shape: `nil`, the
  model's `NotFound` (outcome `error .notFound`), or a `plainErr`; and it formats (`fmt.argOk`: for the `*StatusError`, its `Error()`, which reads the
status's message).

Who would rest on them: `DaemonSetsController.syncNodes`, and so `manage`, `rollingUpdate`,
`updateDaemonSet`, `syncDaemonSet`, `processNextWorkItem`.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.PodControlDefs
public import Spec.fmt.Errorf
public import Proof.k8s_io.apimachinery.pkg.api.errors.Init

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel k8s_io.kubernetes.pkg.controller

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [api_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Assumptions]

/-- **An error `fmt.Errorf` made from a format with no `%w`** (persistent): an `*errors.errorString`
whose `Error()` returns some string. -/
def plainErr (err : GoInterface) : IProp GF :=
  iprop(∃ x : Loc, ⌜err = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x⌝ ∗
    fmt.stringMethodSpec (hG := hG) ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ go!"Error")

/-- **What `IsNotFound` is asked about**: `nil`, a model API error, or a `plainErr`. -/
def notFoundArg (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ (∃ e, errIs err e) ∨ plainErr err)

/-- **Proposed `apierrors.IsNotFound(err)`**: whether `err` is the API's `NotFound`, for the
shapes `notFoundArg` allows. -/
abbrev IsNotFound.proposedSpec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗ notFoundArg err }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.IsNotFound)) (Val #err))
  {{ (b : Bool), RET #b; notFoundArg err ∗ (⌜b = false⌝ ∨ ⌜b = true⌝ ∗ errIs err .notFound) }}

/-- **Proposed `r.DeletePod(ctx, ns, name, ds)`**: today's spec, with the error's shape: `nil`
for an outcome the model returns `nil` for, the model's `NotFound` for that outcome, else a
`plainErr`. -/
abbrev RealPodControl.DeletePod.proposedSpec : Prop :=
  ∀ [ApiDeps] (r : RealPodControl) (γ : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (ctx : GoInterface) (ns name : GoString) (l : Loc) (dd : kd.apps.DaemonSet)
    (Ψ : Except ApiErr Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ ⌜ctx ≠ interface.nil⌝ ∗
      clientIs r.KubeClient' γ cfg ∗ recorderOk r.Recorder' ∗ dsAt l DFrac.discard dd ∗
      deleteAU γ cfg ns name Ψ }}
    (App (App (App (App (Val #(methods RealPodControl.ty go!"DeletePod" #r)) (Val #ctx))
      (Val #ns)) (Val #name))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #l :
        k8s_io.apimachinery.pkg.runtime.Object)))
  {{ (err : GoInterface), RET #err; dsAt l DFrac.discard dd ∗ fmt.argOk (hG := hG) err ∗
      ∃ oc, Ψ oc ∗ (⌜err = interface.nil ∧ ∃ w, oc = .ok w⌝ ∨
        ⌜oc = .error .notFound⌝ ∗ errIs err .notFound ∨ plainErr err) }}

end spec

end dsctl
end EtcdGrove
end Perennial
