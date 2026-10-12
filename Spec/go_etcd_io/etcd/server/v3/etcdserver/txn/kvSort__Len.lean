/-
`kvSort.Len` (`range.go`): the length of the sorter's slice. Lean-first; see `InvRange.lean`, `RangeModel.lean`.
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

/-- `s.Len()`: the length of the slice `s.kvs`. -/
abbrev txn.kvSort.Len.spec : Prop :=
  ∀ (ks : Loc) (sl : GoSlice) (ps : List Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      ks.[kvSort, go!"kvs"] ↦□ sl ∗ sl ↦*{dq} ps }}
    (App (Val (ks @!! go.GoType.PointerType kvSort.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 ps.length); sl ↦*{dq} ps }}

end spec

end EtcdGrove
end Perennial
