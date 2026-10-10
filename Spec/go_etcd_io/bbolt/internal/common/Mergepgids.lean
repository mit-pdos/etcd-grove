module
public import Proof.go_etcd_io.bbolt.internal.common.Init
public import Proof.go_etcd_io.bbolt.internal.common.Model

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

/-- `Mergepgids(dst, a, b)`: with `a` and `b` sorted and `dst` long enough (else it
panics), the first `len(a)+len(b)` elements of `dst` become the sorted union of `a` and
`b` (a sorted permutation of `a ++ b`, which is unique); the rest of `dst` is untouched.
`a` and `b` are only read (they may alias each other, not `dst`). -/
abbrev Mergepgids.spec : Prop :=
  ∀ (dst a b : GoSlice) (ds xs ys : List w64) (qa qb : DFrac),
  xs.length + ys.length ≤ ds.length → PgidsSorted xs → PgidsSorted ys →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗
      dst ↦* ds ∗ a ↦*{qa} xs ∗ b ↦*{qb} ys }}
    (App (App (App (Val #(functions Mergepgids [])) (Val #dst)) (Val #a)) (Val #b))
  {{ (out : List w64), RET #();
      ⌜PgidsSorted out ∧ out.Perm (xs ++ ys)⌝ ∗
      dst ↦* (out ++ ds.drop (xs.length + ys.length)) ∗ a ↦*{qa} xs ∗ b ↦*{qb} ys }}

end spec

end bbolt
end EtcdGrove
end Perennial
