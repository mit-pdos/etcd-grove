/-
`h.pop()` (`wait_time.go`, etcd PR #22495): the min-heap's removal of its least element. Lean-first
(no Rocq counterpart; pr-verify/etcd-22495, 2026-10-17).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.wait.Heap
public import Proof.go_etcd_io.etcd.pkg.v3.wait.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3 waitHeap

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `h.pop()`, on a non-empty heap `*h` (a slice `s` of the min-heap `xs`, of at most `2^62`
elements, so that `pop`'s `2*i + 1` does not overflow): it returns `xs`'s root `t`, its least
element, and `*h` becomes a min-heap `xs'` of the other elements (`t :: xs'` a permutation of
`xs`). -/
abbrev wait.deadlineHeap.pop.spec : Prop :=
  ∀ (hp : Loc) (s : GoSlice) (xs : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ hp ↦ s ∗ s ↦* xs ∗
      ownSliceCap w64 s (DFrac.own 1) ∗ ⌜heapOk xs ∧ 0 < xs.length ∧ xs.length ≤ 2 ^ 62⌝ }}
    (App (Val (hp @!! go.GoType.PointerType wait.deadlineHeap.ty @!! go!"pop")) (Val #()))
  {{ (t : w64), RET #t; ∃ (s' : GoSlice) (xs' : List w64), hp ↦ s' ∗ s' ↦* xs' ∗
      ownSliceCap w64 s' (DFrac.own 1) ∗
      ⌜xs[0]? = some t ∧ (∀ x ∈ xs, uint.Z t ≤ uint.Z x) ∧ heapOk xs' ∧ t :: xs' ≡ₚ xs⌝ }}

end spec

end EtcdGrove
end Perennial
