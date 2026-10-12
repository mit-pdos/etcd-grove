/-
`newTxnResp` (`txn.go`). Lean-first; see `TxnRun.lean`, `InvTxn.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `newTxnResp(rt, txnPath)`, the path `txnPath` of `rt` at a state `s0` (and anything after
it): the response skeleton of the branch the path's first verdict chooses (`txnSkel`: each
operation's wrapper, nested transactions recursively by their verdicts), and the number of
nested transactions. -/
abbrev txn.newTxnResp.spec : Prop :=
  ∀ (rt : Loc) (t : TxnModel) (s0 : List EtcdKv) (pl : GoSlice) (rest : List Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.txnRequestIs rt t ∗ pl ↦*□ (txn.txnPath s0 t ++ rest) }}
    (App (App (Val (@! txn.newTxnResp)) (Val #rt)) (Val #pl))
  {{ (resp : Loc) (n : w64), RET (PairV #resp #n);
      txn.txnSkel s0 resp (txn.txnOk s0 t) (t.branch (txn.txnOk s0 t)) ∗
      txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) ∗
      ⌜n = W64 (txn.nestedCount s0 t : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
