/-
`kvSort.Swap` (`range.go`): exchanges two elements of the sorter's slice. Lean-first; see `InvRange.lean`, `RangeModel.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `s.Swap(i, j)`: the slice `s.kvs` with its `i`-th and `j`-th pointers exchanged. -/
abbrev txn.kvSort.Swap.spec : Prop :=
  ∀ (ks : Loc) (sl : GoSlice) (ps : List Loc) (i j : w64) (a b : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      ks.[kvSort, go!"kvs"] ↦□ sl ∗ sl ↦* ps ∗
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ ps[sint.nat i]? = some a ∧ ps[sint.nat j]? = some b⌝ }}
    (App (App (Val (ks @!! go.GoType.PointerType kvSort.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); sl ↦* (ps.set (sint.nat i) b).set (sint.nat j) a }}

end spec

end EtcdGrove
end Perennial
