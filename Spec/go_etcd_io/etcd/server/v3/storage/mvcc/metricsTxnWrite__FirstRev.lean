/-
`metricsTxnWrite.FirstRev` (`metrics_txn.go`: promoted from the wrapped `TxnWrite`, here a read
transaction's `txnReadWrite` around a `storeTxnRead`, down to `storeTxnCommon.FirstRev`). Lean-first
(no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
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

/-- `mw.FirstRev()` of a read transaction: the compaction revision `crev` it observed (`store.Read`
sets `firstRev` from `s.compactMainRev`; 2026-10-13, unit 6a: `-1` of the frozen transaction, the
instance at `isTxnRead`'s defaults). -/
abbrev mvcc.metricsTxnWrite.FirstRev.spec : Prop :=
  ∀ (trace : Loc) (mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (crev : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxnRead mw s γ trace log rev crev Z }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"FirstRev")) (Val #()))
  {{ RET #(W64 crev : w64); mvcc.isTxnRead mw s γ trace log rev crev Z }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `t.FirstRev()`: a read transaction's compaction revision (of the state it read); a write
transaction's is `0` (`store.Write` sets no first revision). -/
abbrev mvcc.metricsTxnWrite.FirstRev.specC : Prop :=
  ∀ (mw : Loc) (γ : mvcc.MvccName) (trace : Loc) (k : mvcc.MTxn),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace k }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"FirstRev")) (Val #()))
  {{ RET #(match k with
      | .read σ => (W64 σ.crev : w64)
      | .write _ _ => (W64 0 : w64)); mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace k }}

end spec

end EtcdGrove
end Perennial
