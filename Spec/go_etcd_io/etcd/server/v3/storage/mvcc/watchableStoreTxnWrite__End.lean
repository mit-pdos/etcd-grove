/-
`watchableStoreTxnWrite.End` (`watchable_store_txn.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `tw.End()`: with no change, the inner transaction ended (no revision). With changes, the
events of the pending revision (`evsOfRevM`: a delete's key-value gets `ModRevision = rev`;
the key-values are shared with the watchers for good), then under `s.mu` the watchers
notified of them (`notify`, the revision sealed first so that their responses carry the log
that commits it) and the inner transaction ended (the revision committed): the notified log
is the committed one again. The sole writer is back at the committed log, with the reader
slots and the certificate. -/
abbrev mvcc.watchableStoreTxnWrite.End.spec : Prop :=
  ∀ (tw s st : Loc) (γ : mvcc.WsNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (puts deletes putSize : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchTxnWrite tw s st γ ilog pend puts deletes putSize }}
    (App (Val (tw @!! go.GoType.PointerType watchableStoreTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader st γ.st ∗ mvcc.idxCert γ.st.idx (mvcc.commitLog ilog pend) ∗
      mvcc.watchWriter γ (mvcc.commitLog ilog pend) }}

end spec

end EtcdGrove
end Perennial
