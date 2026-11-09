/-
`newTxnResp(rt, txnPath)` (`txn.go`), internal (`txn`, recursively): mirrors the code (`respSkel`;
the count of nested transactions on the taken path, the path's length less one). Old spec: same.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `newTxnResp(rt, path)`, `path` starting with `t`'s verdicts at `s`: the response tree for the
taken branch, and the number of nested transactions on the taken path. -/
def newTxnResp.spec : Prop :=
  ∀ (rt : Loc) (dq : DFrac) (t : TxnReq) (s : EtcdModel.Store) (path : GoSlice) (rest : List Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txnReqOwn rt dq t ∗ path ↦*□ (txnPathOf t s ++ rest) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.newTxnResp)) (Val #rt)) (Val #path))
  {{ (resp : Loc) (n : w64), RET (PairV #resp #n); txnReqOwn rt dq t ∗
      respSkel resp s (cmpsHold t.compare s) (if cmpsHold t.compare s then t.success else t.failure) ∗
      ⌜n = W64 ((txnPathOf t s).length - 1)⌝ }}

end spec
end Txn
end EtcdGrove
end Perennial
