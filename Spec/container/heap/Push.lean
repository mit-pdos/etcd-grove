/-
`heap.Push(h, x)` (`container/heap`, names only: the trust boundary). Lean-first (no Rocq
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

/-- `heap.Push(h, x)` calls `h.Push(x)` and then sifts the last element up (`up(h, h.Len()-1)`:
`Less` and `Swap` at indices in range): the contents end a permutation of `xs ++ [a]`. -/
abbrev heap.Push.spec : Prop :=
  ∀ (A : Type) (h : GoInterfaceOk) (R : List A → IProp GF) (E : GoInterface → A → IProp GF)
    (xs : List A) (x : GoInterface) (a : A),
  {{ isPkgInit (PROP := IProp GF) pkg_id.container.heap ∗ heap.heapIface h R E ∗ R xs ∗ E x a }}
    (App (App (Val (@! container.heap.Push)) (Val #(GoInterface.ok h))) (Val #x))
  {{ RET #(); ∃ ys : List A, R ys ∗ ⌜ys.Perm (xs ++ [a])⌝ }}

end spec

end EtcdGrove
end Perennial
