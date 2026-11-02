/-
`NewReadOnlyTxnWrite` (`kv.go`). Lean-first (no Rocq counterpart); see `InvRoTxn.lean`.

-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRoTxn
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

/-- `NewReadOnlyTxnWrite(txn)` of a read transaction (`store.Read`'s): a `txnReadWrite`
wrapping it, as a `TxnWrite`. -/
abbrev mvcc.NewReadOnlyTxnWrite.spec : Prop :=
  ∀ (trace : Loc) (mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (crev : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isTxnRead mw s γ trace log rev crev Z }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewReadOnlyTxnWrite))
      (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface)))
  {{ (trw : Loc), RET #(interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw : GoInterface);
      mvcc.isRoTxnWrite trw s γ trace log rev crev Z }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `NewReadOnlyTxnWrite(t)` of a read transaction at `σ`: a `TxnWrite` over it. -/
abbrev mvcc.NewReadOnlyTxnWrite.specC : Prop :=
  ∀ (mw : Loc) (γ : mvcc.MvccName) (trace : Loc) (σ : mvcc.MvccState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace (.read σ) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewReadOnlyTxnWrite))
      (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface)))
  {{ (trw : Loc), RET #(interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw : GoInterface);
      mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw) γ trace (.read σ) }}

end spec

end EtcdGrove
end Perennial
