/-
`apierrors.SuggestsClientDelay(err)` (`k8s.io/apimachinery/pkg/api/errors/errors.go:791-805`,
names-only): `(seconds, true)` when the error asks the client to retry later. Of a `*StatusError`
(view `.status st _`): with nil details, `(0, false)`; with details `d`, `(d.RetryAfterSeconds,
true)` if the reason is `ServerTimeout` or `d.RetryAfterSeconds > 0`, else `(0, false)`
(`delayV`). Of a `.plain` error, `(0, false)`. Stated, as `IsTimeout.spec`, as a post every view of
the error answers, under `apiErrOk err`. Called by the checker's `Model.validateGet` and
`validateList` on every stale read's output error (k8s 7g, `notes/k8s-7g-trust.md`): `nil`, a
`*storage.StorageError` (inner `nil` or an `errors.New`), an `errors.New`, or storage's too-large
`*StatusError`; the first three are `.plain` in the extended view (proposal V of the step 1
report). Its axiom will be `apierrors.SuggestsClientDelay.wp_proof`.

Faithful: `t, ok := err.(APIStatus)`; if not, `errors.As(err, &t)`; then, if `t.Status().Details
!= nil`, the reason test and the `RetryAfterSeconds > 0` test, each returning
`int(RetryAfterSeconds)` (an `int32` sign-extended); otherwise `(0, false)`. `Status()` of a
`*StatusError` is its `ErrStatus` (`errors.go:75-79`), so the answer reads the struct and the
details' pointee, both held read-only by the view (`statusDetailsAt`); a typed nil `*StatusError`
panics in `Status()`, which `apiErrOk` excludes. A `.plain` error is no `APIStatus` and
`errors.As` finds none in it (nil: `As` returns false; a leaf: nothing to unwrap; a wrapper:
its `Unwrap` returns nil or a leaf). Go evidence: `examples/k8s/etcd3/trustspecs_test.go`
`TestSuggestsClientDelay` (the checker's errors; too-large with retry 0 is `(0, false)`, with 2
`(2, true)`; `NewServerTimeout`, `NewTooManyRequests` with and without retry; nil details; the
answer equals `delayV` on every `*StatusError`; a typed nil `*StatusError` panics),
`TestStorageErrorNotAPIStatus`. Lean-first.
-/
module

public import Proof.k8s_io.apimachinery.pkg.api.errors.View

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI

section pure
variable [GooseExts]

/-- `SuggestsClientDelay`'s answer on a status with details `d` (`errors.go:794-802`). -/
def delayV (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
    (d : k8s_io.apimachinery.pkg.apis.«meta».v1.StatusDetails) : w64 × Bool :=
  if st.Reason' = go!"ServerTimeout" ∨ 0 < sint.Z d.RetryAfterSeconds' then
    (W64 (sint.Z d.RetryAfterSeconds'), true)
  else (W64 0, false)

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- See the file header. -/
abbrev SuggestsClientDelay.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗ apiErrOk err }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.SuggestsClientDelay)) (Val #err))
  {{ (n : w64) (b : Bool), RET (PairV #n #b); □ ∀ w, apiErrAt err w -∗
      match w with
      | .plain => ⌜n = W64 0 ∧ b = false⌝
      | .status st _ => ⌜st.Details' = null ∧ n = W64 0 ∧ b = false⌝ ∨
          ∃ d, st.Details' ↦□ d ∗ ⌜(n, b) = delayV st d⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
