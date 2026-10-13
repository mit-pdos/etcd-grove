/-
`container/heap`'s contract on its `heap.Interface` argument (2026-10-13, unit 9 of the backend:
the lessor's expiry notifier). Lean-first (no Rocq counterpart).

`container/heap` is a standard-library package Perennial does not translate (names only here),
so `heap.Push` and `heap.Fix` are the trust boundary (`Spec/container/heap/`): their specs say
what the Go functions do with the interface's methods, abstracted over the heap's contents
`R xs` (a list of elements of any type `A`): `Len` returns the length, `Less(i, j)` and
`Swap(i, j)` are called only at indices in range (`Swap` swaps the two elements, `listSwap`),
`Push(x)` appends the element `x` stands for (`E x a`). The heap order is not tracked: the
results are permutations of the contents.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace heap

open Iris Iris.BI Iris.ProofMode

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The `heap.Interface` value `h`** over the contents `R xs` (persistent): `Len()` returns
`len xs`; `Less(i, j)`, for `i`, `j` in range, returns and changes nothing; `Swap(i, j)`, for
`i`, `j` in range, swaps the two elements; `Push(x)`, for an `x` standing for `a` (`E x a`),
appends `a`. -/
def heapIface {A : Type} (h : GoInterfaceOk) (R : List A → IProp GF)
    (E : GoInterface → A → IProp GF) : IProp GF :=
  iprop(□ (∀ xs : List A,
      {{ R xs }} (App (Val #(methods h.ty go!"Len" h.v)) (Val #()))
      {{ (n : w64), RET #n; R xs ∗ ⌜sint.Z n = (xs.length : Int)⌝ }}) ∗
    □ (∀ (xs : List A) (i j : w64),
      {{ R xs ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < xs.length ∧ 0 ≤ sint.Z j ∧ sint.Z j < xs.length⌝ }}
        (App (App (Val #(methods h.ty go!"Less" h.v)) (Val #i)) (Val #j))
      {{ (b : Bool), RET #b; R xs }}) ∗
    □ (∀ (xs : List A) (i j : w64),
      {{ R xs ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < xs.length ∧ 0 ≤ sint.Z j ∧ sint.Z j < xs.length⌝ }}
        (App (App (Val #(methods h.ty go!"Swap" h.v)) (Val #i)) (Val #j))
      {{ RET #(); R (lease.listSwap xs (sint.nat i) (sint.nat j)) }}) ∗
    □ (∀ (xs : List A) (x : GoInterface) (a : A),
      {{ R xs ∗ E x a }} (App (Val #(methods h.ty go!"Push" h.v)) (Val #x))
      {{ RET #(); R (xs ++ [a]) }}))

instance heapIface_persistent {A : Type} (h : GoInterfaceOk) (R : List A → IProp GF)
    (E : GoInterface → A → IProp GF) : Persistent (heapIface h R E) := by
  unfold heapIface; infer_instance

end defs

end heap
end EtcdGrove
end Perennial
