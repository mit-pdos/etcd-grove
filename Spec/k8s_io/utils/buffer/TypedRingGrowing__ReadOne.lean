/-
`(*TypedRingGrowing[T]).ReadOne()` (`ring_growing.go:62`), at `T = any`: the oldest value removed, or `(nil, false)` if empty. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the listeners' buffer).
-/
module

public import Proof.k8s_io.utils.buffer.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace buffer

open Iris Iris.BI k8s_io.utils.buffer

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.buffer.Assumptions]

/-- **`r.ReadOne()`** on the ring holding `q`: `(nil, false)` and the ring unchanged if `q` is
empty; otherwise `q`'s first value and `true`, the ring holding the rest. -/
abbrev TypedRingGrowing.ReadOne.spec : Prop :=
  ∀ (r : Loc) (q : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.buffer ∗ ownRing r q }}
    (App (Val (r @!! go.GoType.PointerType (TypedRingGrowing.ty go.any) @!! go!"ReadOne"))
      (Val #()))
  {{ (v : GoInterface) (ok : Bool), RET (PairV #v #ok);
      match q with
      | [] => ⌜v = interface.nil ∧ ok = false⌝ ∗ ownRing r []
      | x :: q' => ⌜v = x ∧ ok = true⌝ ∗ ownRing r q' }}

end spec

end buffer
end EtcdGrove
end Perennial
