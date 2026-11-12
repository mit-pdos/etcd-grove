/-
`Pgids.Merge`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Proof.go_etcd_io.bbolt.internal.common.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `s.Merge(b)`: the sorted union of the sorted `s` and `b` (a sorted permutation of their
concatenation). If `s` is empty it returns `b` itself, else if `b` is empty `s` itself; otherwise
a new slice (`make`, then `Mergepgids`). `s` and `b` are only read. -/
abbrev Pgids.Merge.spec : Prop :=
  ∀ (s b : GoSlice) (xs ys : List w64) (qa qb : DFrac),
  PgidsSorted xs → PgidsSorted ys → xs.length + ys.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦*{qa} xs ∗ b ↦*{qb} ys }}
    (App (Val (s @!! Pgids.ty @!! go!"Merge")) (Val #b))
  {{ (r : GoSlice) (out : List w64), RET #r;
      ⌜PgidsSorted out ∧ out.Perm (xs ++ ys)⌝ ∗ s ↦*{qa} xs ∗ b ↦*{qb} ys ∗
      (⌜xs = [] ∧ r = b ∧ out = ys⌝ ∨ ⌜xs ≠ [] ∧ ys = [] ∧ r = s ∧ out = xs⌝ ∨
        (⌜xs ≠ [] ∧ ys ≠ []⌝ ∗ r ↦* out ∗ ownSliceCap w64 r (DFrac.own 1))) }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
