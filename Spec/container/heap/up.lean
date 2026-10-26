/-
`heap.up(h, j)` (`container/heap`, unexported: `Push` and `Fix` call it). Lean-first (no Rocq
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

/-- `heap.up(h, j)`, `j` in range, sifts the element at `j` up (`Less` and `Swap` at `j` and its
parent `(j-1)/2`, both in range): the contents end a permutation of `xs`. -/
abbrev heap.up.spec : Prop :=
  ∀ (A : Type) (h : GoInterfaceOk) (R : List A → IProp GF) (E : GoInterface → A → IProp GF)
    (xs : List A) (j : w64),
  0 ≤ sint.Z j → sint.Z j < xs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.container.heap ∗ heap.heapIface h R E ∗ R xs }}
    (App (App (Val (@! container.heap.up)) (Val #(GoInterface.ok h))) (Val #j))
  {{ RET #(); ∃ ys : List A, R ys ∗ ⌜ys.Perm xs⌝ }}

end spec

end EtcdGrove
end Perennial
