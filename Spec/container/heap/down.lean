/-
`heap.down(h, i0, n)` (`container/heap`, unexported: `Fix` calls it). Lean-first (no Rocq
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `heap.down(h, i0, n)`, `i0` non-negative and `n` at most the length, sifts the element at `i0`
down within the first `n` (`Less` and `Swap` at an index and its children below `n`; nothing when
`i0`'s first child is not below `n`): it returns whether the element moved, and the contents end a
permutation of `xs`. (prove-smallinits, 2026-11-20: `n` at most the length, not equal to it, and
`i0` any non-negative index, for `Pop`'s `down(h, 0, n-1)`; until then `i0 < len` and `n = len`.) -/
abbrev heap.down.spec : Prop :=
  ∀ (A : Type) (h : GoInterfaceOk) (R : List A → IProp GF) (E : GoInterface → A → IProp GF)
    (xs : List A) (i0 n : w64),
  0 ≤ sint.Z i0 → 0 ≤ sint.Z n → sint.Z n ≤ xs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.container.heap ∗ heap.heapIface h R E ∗ R xs }}
    (App (App (App (Val (@! container.heap.down)) (Val #(GoInterface.ok h))) (Val #i0)) (Val #n))
  {{ (b : Bool), RET #b; ∃ ys : List A, R ys ∗ ⌜ys.Perm xs⌝ }}

end spec

end EtcdGrove
end Perennial
