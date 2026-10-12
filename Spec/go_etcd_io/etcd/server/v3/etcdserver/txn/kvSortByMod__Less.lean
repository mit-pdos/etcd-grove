/-
`kvSortByMod.Less` (`range.go`): Go's `(a - b) < 0` on the two `ModRevision`s, the signed order on non-negative values (`kvOk`: no overflow, `sub_neg_iff`). Lean-first; see `InvRange.lean`, `RangeModel.lean`.
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

/-- `s.Less(i, j)` of the sorter `sp` (its `kvSort` `ks`, its slice `sl` holding the pointers of
`l`, owned): `kvLtBy 3` of the `i`-th and `j`-th key-values. -/
abbrev txn.kvSortByMod.Less.spec : Prop :=
  ∀ (sp ks : Loc) (sl : GoSlice) (l : List (Loc × EtcdKv)) (dq : DFrac) (i j : w64)
    (a b : Loc × EtcdKv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      sp.[kvSortByMod, go!"kvSort"] ↦□ ks ∗ ks.[kvSort, go!"kvs"] ↦□ sl ∗
      sl ↦*{dq} l.map Prod.fst ∗ txn.kvsAt l ∗
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b ∧ kvOk a.2 ∧ kvOk b.2⌝ }}
    (App (App (Val (sp @!! go.GoType.PointerType kvSortByMod.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ RET #(txn.kvLtBy (W64 3) a.2 b.2); sl ↦*{dq} l.map Prod.fst ∗ txn.kvsAt l }}

end spec

end EtcdGrove
end Perennial
