/-
## `Pgids.Merge(b)` (`internal/common/page.go`)

**Users.** freelist array's `mergeSpans` (`f.ids = Pgids(f.ids).Merge(ids)`). Snippet `ReqMergePgids`.
**Proof sketch.** the two empty cases return an argument; else `make` and `Mergepgids`.
**Changes.** from `specs-ref`'s file of the same name: the result named as `sortPgids (xs ++ ys)` (unique: a sorted permutation).
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `s.Merge(b)`: the sorted merge of the sorted `s` and `b`: `b` itself if `s` is empty, else `s` itself if `b` is, else a new slice. -/
def Pgids.Merge.spec : Prop :=
  ∀ (s b : GoSlice) (xs ys : List Pgid) (qa qb : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦*{qa} xs ∗ b ↦*{qb} ys ∗
      ⌜pgidsSorted xs ∧ pgidsSorted ys ∧ xs.length + ys.length < 2 ^ 63⌝ }}
    (App (Val (s @!! go_etcd_io.bbolt.internal.common.Pgids.ty @!! go!"Merge")) (Val #b))
  {{ (r : GoSlice), RET #r; s ↦*{qa} xs ∗ b ↦*{qb} ys ∗
      (⌜xs = [] ∧ r = b⌝ ∨ ⌜xs ≠ [] ∧ ys = [] ∧ r = s⌝ ∨
        (⌜xs ≠ [] ∧ ys ≠ []⌝ ∗ r ↦* sortPgids (xs ++ ys) ∗ ownSliceCap Pgid r (DFrac.own 1))) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
