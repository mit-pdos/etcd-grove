module
public import Spec.go_etcd_io.bbolt.internal.common.Mergepgids

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `s.Merge(b)`: the sorted union of `s` and `b`, which are sorted. If one is empty the
other is returned (the same slice); otherwise a new slice. -/
abbrev Pgids.Merge.spec : Prop :=
  ∀ (s b : GoSlice) (xs ys : List w64) (qa qb : DFrac),
  PgidsSorted xs → PgidsSorted ys → xs.length + ys.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦*{qa} xs ∗ b ↦*{qb} ys }}
    (App (Val (s @!! Pgids.ty @!! go!"Merge")) (Val #b))
  {{ (r : GoSlice) (out : List w64), RET #r;
      ⌜PgidsSorted out ∧ out.Perm (xs ++ ys)⌝ ∗ s ↦*{qa} xs ∗ b ↦*{qb} ys ∗
      (⌜xs = [] ∧ r = b ∧ out = ys⌝ ∨ ⌜xs ≠ [] ∧ ys = [] ∧ r = s ∧ out = xs⌝ ∨ r ↦* out) }}

end spec

end bbolt
end EtcdGrove
end Perennial
