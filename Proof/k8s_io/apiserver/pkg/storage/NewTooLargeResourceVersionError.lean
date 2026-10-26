/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/NewTooLargeResourceVersionError.lean`. Lean-first (no
Rocq counterpart).

Unfinished (KEP-6404, `notes/kep-6404-plan.md`): `fmt.Sprintf`'s message, `apierrors.NewTimeoutError`
(names-only: a trust-boundary spec, which must give the status error's `Details`, non-nil, to
write their `Causes`), and the slice literal of the cause.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.NewTooLargeResourceVersionError.wp_proof :
    storage.NewTooLargeResourceVersionError.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
