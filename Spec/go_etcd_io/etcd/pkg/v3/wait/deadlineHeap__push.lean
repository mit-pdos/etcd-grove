/-
`h.push(d)` (`wait_time.go`, etcd PR #22495): the min-heap's insertion. Lean-first (no Rocq
counterpart; pr-verify/etcd-22495, 2026-10-17).
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

/-- `h.push(d)`, on the heap `*h` (a slice `s` of the min-heap `xs`, `heapOk`, with its capacity):
`*h` becomes a min-heap of `xs`'s elements and `d` (a permutation of `xs ++ [d]`), of fewer than
`2^62` elements (Go's `append` never builds a longer `[]uint64`:
`Proof/go_etcd_io/etcd/pkg/v3/wait/HeapAppend.lean`). -/
abbrev wait.deadlineHeap.push.spec : Prop :=
  ∀ (hp : Loc) (s : GoSlice) (xs : List w64) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ hp ↦ s ∗ s ↦* xs ∗
      ownSliceCap w64 s (DFrac.own 1) ∗ ⌜heapOk xs⌝ }}
    (App (Val (hp @!! go.GoType.PointerType wait.deadlineHeap.ty @!! go!"push")) (Val #d))
  {{ RET #(); ∃ (s' : GoSlice) (xs' : List w64), hp ↦ s' ∗ s' ↦* xs' ∗
      ownSliceCap w64 s' (DFrac.own 1) ∗
      ⌜heapOk xs' ∧ xs' ≡ₚ xs ++ [d] ∧ xs'.length < 2 ^ 62⌝ }}

end spec

end EtcdGrove
end Perennial
