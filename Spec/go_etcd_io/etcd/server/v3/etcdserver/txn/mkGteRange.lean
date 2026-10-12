/-
`txn.mkGteRange` (delete.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `mkGteRange(rangeEnd)`: `[0]` ("every key from the key on", gRPC sends an empty range end
as `nil`) becomes the empty, non-`nil` slice `[]byte{}`; any other range end is returned as
it is. -/
abbrev txn.mkGteRange.spec : Prop :=
  ∀ (rangeEnd : GoSlice) (e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ rangeEnd ↦*□ e }}
    (App (Val (@! txn.mkGteRange)) (Val #rangeEnd))
  {{ (r : GoSlice), RET #r; r ↦*□ (if e = [W8 0] then [] else e) ∗
      ⌜if e = [W8 0] then r ≠ slice.nil else r = rangeEnd⌝ }}

end spec

end EtcdGrove
end Perennial
