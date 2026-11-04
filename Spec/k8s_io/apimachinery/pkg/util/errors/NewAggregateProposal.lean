/-
**A proposal** (the DaemonSet autoverify run, track B, 2026-11-04; review 1's M1): what the
DaemonSet controller's proofs need of `utilerrors.NewAggregate(errlist)`, stated as a candidate
replacement of the named hypothesis `NewAggregate.spec` (pending approval, Stage 4). Not used by
any proof yet; nothing rests on it.

The code (`k8s.io/apimachinery/pkg/util/errors/errors.go`): `nil` for an empty list or one of
`nil`s, else `aggregate(errs)`, a new slice of the non-`nil` errors, whose `Error()` calls each
one's `Error()` (and keeps no reference to the list). So:

* `nil` exactly when every element is `nil`: `ClaimPods` and `ClaimControllerRevisions` return
  `NewAggregate(nil)`, which the callers compare with `nil` (their specs' `err = nil`);
* the aggregate formats, given that its elements do: `syncNodes` returns it, and its caller
  formats it (`fmt.argOk`). The elements' `fmt.argOk` are consumed (the aggregate's `Error()`
  calls theirs).

Who would rest on it: `PodControllerRefManager.ClaimPods`, `ControllerRevisionControllerRefManager.
ClaimControllerRevisions` (their `err = nil`) and `DaemonSetsController.syncNodes` (its `fmt.argOk
err`), so `manage`, `rollingUpdate`, `updateDaemonSet`, `syncDaemonSet`, `processNextWorkItem`.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace utilerrors

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Proposed `NewAggregate(errs)`**: `nil` exactly for a list of `nil`s; a formattable error
otherwise; the list kept. -/
abbrev NewAggregate.proposedSpec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (es : List GoInterface),
  {{ s ↦*{dq} es ∗ fmt.argsOk (hG := hG) es }}
    (App (Val (@! k8s_io.apimachinery.pkg.util.errors.NewAggregate)) (Val #s))
  {{ (a : GoInterface), RET #a; s ↦*{dq} es ∗
      ⌜a = (interface.nil : GoInterface) ↔ ∀ e, e ∈ es → e = (interface.nil : GoInterface)⌝ ∗ fmt.argOk (hG := hG) a }}

end spec

end utilerrors
end EtcdGrove
end Perennial
