/-
`mkGteRange` (`delete.go`; called by `executeRange`, `deleteRange`, `applyCompare`).
Lean-first; see `InvRange.lean`, `RangeModel.lean`.
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

/-- `mkGteRange(rangeEnd)`: the end key mvcc reads, `srvEnd` of the request's range end
(`rangeEndOf`): `[]byte{0}` ("every key from the key on") becomes the empty non-`nil` slice
`[]byte{}`, which mvcc reads as no upper bound; a `nil` slice stays `nil` (the key alone). -/
abbrev txn.mkGteRange.spec : Prop :=
  ∀ (sl : GoSlice) (e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ sl ↦*□ e }}
    (App (Val (@! txn.mkGteRange)) (Val #sl))
  {{ (sl' : GoSlice) (e' : GoString), RET #sl'; sl' ↦*□ e' ∗
      ⌜txn.srvEnd (txn.rangeEndOf sl e) = (decide (sl' = slice.nil), e')⌝ }}

end spec

end EtcdGrove
end Perennial
