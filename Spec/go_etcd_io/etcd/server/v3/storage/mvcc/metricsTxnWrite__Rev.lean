/-
`metricsTxnWrite.Rev` (`metrics_txn.go`: promoted from the wrapped `TxnWrite`: a read
transaction's `txnReadWrite` around a `storeTxnRead`, down to `storeTxnCommon.Rev`, or a write
transaction's `storeTxnWrite.Rev`). Lean-first
(no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `mw.Rev()` of a transaction of either kind: the revision it began at (`TxnKind.beginRev`: a
read transaction's revision, a write transaction's committed log's last). -/
abbrev mvcc.metricsTxnWrite.Rev.spec : Prop :=
  ∀ (trace : Loc) (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind) (crev : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxn mw s γ trace kind crev Z }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Rev")) (Val #()))
  {{ RET #(kind.beginRev : w64); mvcc.isTxn mw s γ trace kind crev Z }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `t.Rev()`: the revision of the state the transaction began at. -/
abbrev mvcc.metricsTxnWrite.Rev.specC : Prop :=
  ∀ (mw : Loc) (γ : mvcc.MvccName) (trace : Loc) (k : mvcc.MTxn),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace k }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Rev")) (Val #()))
  {{ RET #(W64 (k.state.rev : Int) : w64); mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace k }}

end spec

end EtcdGrove
end Perennial
