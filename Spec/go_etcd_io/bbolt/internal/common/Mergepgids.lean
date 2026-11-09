/-
## `Mergepgids(dst, a, b)` (`internal/common/page.go`)

**Users.** freelist `Copyall` (and `Write`, through it); `Pgids.Merge`. Snippet `ReqMergePgids`.
**Proof sketch.** the length check; `copy` when one side is empty; else the loop over `lead`/`follow` with `sort.Search` (Perennial's), appending into `dst[:0]` within its capacity; its invariant: `merged` is a sorted permutation of the consumed prefixes, `follow` and the rest of `lead` sorted and above it.
**Changes.** from `specs-ref`'s file of the same name (unchanged but the premises moved into the precondition).
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

/-- `Mergepgids(dst, a, b)`: with `a`, `b` sorted and `dst` long enough (it panics otherwise), the first `len(a)+len(b)` elements of `dst` become the sorted merge of `a` and `b`; the rest is untouched; `a`, `b` are only read. -/
def Mergepgids.spec : Prop :=
  ∀ (dst a b : GoSlice) (ds xs ys : List Pgid) (qa qb : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ dst ↦* ds ∗ a ↦*{qa} xs ∗ b ↦*{qb} ys ∗
      ⌜xs.length + ys.length ≤ ds.length ∧ pgidsSorted xs ∧ pgidsSorted ys⌝ }}
    (App (App (App (Val (@! go_etcd_io.bbolt.internal.common.Mergepgids)) (Val #dst)) (Val #a)) (Val #b))
  {{ RET #(); dst ↦* (sortPgids (xs ++ ys) ++ ds.drop (xs.length + ys.length)) ∗
      a ↦*{qa} xs ∗ b ↦*{qb} ys }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
