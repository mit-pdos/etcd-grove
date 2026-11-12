/-
`heap.Init(h)` (`container/heap`, names only: the trust boundary; the file is `Init_` since `Init.lean` is the package's initialization). Lean-first; see
`Proof/container/heap/Defs.lean`. For client-go's delaying queue.
-/
module

public import Proof.container.heap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `heap.Init(h)` heapifies with `Len`, `Less` and `Swap` (`down(h, i, n)` for `i` from
`n/2 - 1` down to `0`: indices in range): the contents end a permutation of `xs`. -/
abbrev heap.Init_.spec : Prop :=
  ∀ (A : Type) (h : GoInterfaceOk) (R : List A → IProp GF) (E : GoInterface → A → IProp GF)
    (xs : List A),
  {{ isPkgInit (PROP := IProp GF) pkg_id.container.heap ∗ heap.heapIface h R E ∗ R xs }}
    (App (Val (@! container.heap.Init)) (Val #(GoInterface.ok h)))
  {{ RET #(); ∃ ys : List A, R ys ∗ ⌜ys.Perm xs⌝ }}

end spec

end EtcdGrove
end Perennial
