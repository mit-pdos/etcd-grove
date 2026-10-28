/-
`heap.Pop(h)` (`container/heap`, names only: the trust boundary). Lean-first; see
`Proof/container/heap/Defs.lean`. For client-go's delaying queue.
-/
module

public import Proof.container.heap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`h.Pop()`** (persistent): on contents `xs ++ [a]`, removes the last element and returns a
value standing for it (`E x a`). -/
def heap.heapPopIface {A : Type} (h : GoInterfaceOk) (R : List A → IProp GF)
    (E : GoInterface → A → IProp GF) : IProp GF :=
  iprop(□ (∀ (xs : List A) (a : A),
    {{ R (xs ++ [a]) }} (App (Val #(methods h.ty go!"Pop" h.v)) (Val #()))
    {{ (x : GoInterface), RET #x; R xs ∗ E x a }}))

instance heap.heapPopIface_persistent {A : Type} (h : GoInterfaceOk) (R : List A → IProp GF)
    (E : GoInterface → A → IProp GF) : Persistent (heap.heapPopIface h R E) := by
  unfold heap.heapPopIface; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `heap.Pop(h)` on non-empty contents: `n := h.Len() - 1; h.Swap(0, n); down(h, 0, n);
return h.Pop()` (indices in range): returns a value standing for one of the elements, the
contents the others. -/
abbrev heap.Pop.spec : Prop :=
  ∀ (A : Type) (h : GoInterfaceOk) (R : List A → IProp GF) (E : GoInterface → A → IProp GF)
    (xs : List A),
  xs ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.container.heap ∗ heap.heapIface h R E ∗
      heap.heapPopIface h R E ∗ R xs }}
    (App (Val (@! container.heap.Pop)) (Val #(GoInterface.ok h)))
  {{ (x : GoInterface), RET #x; ∃ (ys : List A) (a : A), R ys ∗ E x a ∗ ⌜(ys ++ [a]).Perm xs⌝ }}

end spec

end EtcdGrove
end Perennial
