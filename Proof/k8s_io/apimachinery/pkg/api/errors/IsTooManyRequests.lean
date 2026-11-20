/-
The trust boundary of `apierrors.IsTooManyRequests` (see its spec). (k8s 7g, decided by
etcd-grove-03 2026-11-19: option A.) Not proved from its body: `reasonAndCodeForError` falls back
to `errors.As(err, &status)` on the `.plain` views, and Perennial's `errors.As.spec` (an axiom:
reflection) allows any result there, so a proof would need further `errors.As` axioms (on `nil`
and on a one-level wrapper of a leaf) in place of this one. Go evidence:
`examples/k8s/etcd3/trustspecs_test.go` `TestIsTooManyRequests`, `TestStatusChecksPlain`,
`TestPlainWrapperTypedNil`.
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.IsTooManyRequests

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

axiom IsTooManyRequests.wp_proof : IsTooManyRequests.spec (GF := GF) (hG := hG)

end proof

end apierrors
end EtcdGrove
end Perennial
