/-
`storeTxnWrite.End` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

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

/-- `tw.End()` ends the write transaction: with a change, the pending revision is committed
(`currentRev++` and the batch transaction's write-back, under `s.revMu`), certified
(`idxCert` of `commitLog`); the transaction's tokens are the caller's again, and so is its
revision token if no revision was made (`pend = []`). `Unlock` takes the batch lock's
invariant `P` (the store's, `hookIs`) back. -/
abbrev mvcc.storeTxnWrite.End.spec : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (P : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.storeTxnWriteIs tw s γ ilog pend ∗
      mvcc.hookIs γ P f ∗ P }}
    (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ ∗ mvcc.idxCert γ.idx (mvcc.commitLog ilog pend) ∗
      (if pend = [] then mvcc.revToken γ else iprop(True)) }}

end spec

end EtcdGrove
end Perennial
