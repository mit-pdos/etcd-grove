/-
`heap.Fix(h, i)` (`container/heap`, names only: the trust boundary). Lean-first (no Rocq
counterpart); see `Proof/container/heap/Defs.lean`.
-/
module

public import Proof.container.heap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `heap.Fix(h, i)`, `i` in range, sifts the element at `i` down or up (`down(h, i, h.Len())`,
`up(h, i)`: `Less` and `Swap` at indices in range; Go's `heap.Fix` with `i` out of range would
call `Less` out of range): the contents end a permutation of `xs`. -/
abbrev heap.Fix.spec : Prop :=
  ∀ (A : Type) (h : GoInterfaceOk) (R : List A → IProp GF) (E : GoInterface → A → IProp GF)
    (xs : List A) (i : w64),
  0 ≤ sint.Z i → sint.Z i < xs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.container.heap ∗ heap.heapIface h R E ∗ R xs }}
    (App (App (Val (@! container.heap.Fix)) (Val #(GoInterface.ok h))) (Val #i))
  {{ RET #(); ∃ ys : List A, R ys ∗ ⌜ys.Perm xs⌝ }}

end spec

end EtcdGrove
end Perennial
