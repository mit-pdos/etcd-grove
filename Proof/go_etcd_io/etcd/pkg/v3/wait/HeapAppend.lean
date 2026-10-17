/-
**Trust boundary**: Go's `append` on `pkg/wait`'s `deadlineHeap` (a `[]uint64`, etcd PR #22495)
never returns a slice of `2^62` elements or more. Lean-first (no Rocq counterpart;
pr-verify/etcd-22495, 2026-10-17).

Why it is needed: `deadlineHeap.pop` computes the left child `2*i + 1` of a node `i < len(s)` in
`int`, which overflows (and then indexes the slice at a negative index, a panic) once `len(s)`
exceeds `2^62`; Perennial's `slices.siftDownOrdered` (the standard library's heap sort) has the same
code and takes `len(data) ≤ 2^62` as a premise. Here the slice is built by `push`'s `append`s, one
per new deadline of `Wait`, whose contract (`isWaitTime`) takes no premise, so the bound has to come
from `append`.

Why it is believed: Go's runtime refuses (`growslice` panics, "len out of range") to grow a slice
whose backing array would exceed `maxAlloc` bytes, `2^48` on every 64-bit platform Go supports
(`runtime/malloc.go`), so a `[]uint64` from `append` has at most `2^45` elements, far below `2^62`.
Perennial's model of `append` only assumes that the new length fits an `int` (fewer than `2^63`
elements: `wp_sumAssumeNoOverflowSigned`), as its model of maps assumes fewer than `2^63` keys
(`wp_map_len_lt`); the general fix is a model assumption of Go's allocation bound in Perennial
(recorded in `notes/STATUS.md` of this branch), not made here.

The statement is Perennial's `wp_slice_append` at `deadlineHeap.ty`, with the bound added.
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.wait

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section axioms
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

/-- **`append` on a `deadlineHeap` returns fewer than `2^62` elements** (see the file header). -/
axiom wait.deadlineHeap.append_len_bound (sl : GoSlice) (vs : List w64) (sl2 : GoSlice)
    (vs' : List w64) (dq : DFrac) :
    {{ (sl ↦* vs ∗ ownSliceCap w64 sl (DFrac.own 1) ∗ sl2 ↦*{dq} vs' : IProp GF) }}
      (App (App (Val #(functions go.append [wait.deadlineHeap.ty])) (Val #sl)) (Val #sl2))
    {{ (s' : GoSlice), RET #s';
        s' ↦* (vs ++ vs') ∗ ownSliceCap w64 s' (DFrac.own 1) ∗ sl2 ↦*{dq} vs' ∗
        ⌜(vs ++ vs').length < 2 ^ 62⌝ }}

end axioms

end EtcdGrove
end Perennial
