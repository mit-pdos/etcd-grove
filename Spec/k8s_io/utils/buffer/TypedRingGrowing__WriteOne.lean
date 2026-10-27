/-
`(*TypedRingGrowing[T]).WriteOne(data)` (`ring_growing.go:80`), at `T = any`: the value appended, the storage doubled if full. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the listeners' buffer).
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

/-- **`r.WriteOne(x)`** on the ring holding `q`, with fewer than `2^61` values (so the doubled
storage stays below `2^62`): the ring holds `q ++ [x]`. -/
abbrev TypedRingGrowing.WriteOne.spec : Prop :=
  ∀ (r : Loc) (q : List GoInterface) (x : GoInterface), q.length < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.buffer ∗ ownRing r q }}
    (App (Val (r @!! go.GoType.PointerType (TypedRingGrowing.ty go.any) @!! go!"WriteOne"))
      (Val #x))
  {{ RET #(); ownRing r (q ++ [x]) }}

end spec

end buffer
end EtcdGrove
end Perennial
