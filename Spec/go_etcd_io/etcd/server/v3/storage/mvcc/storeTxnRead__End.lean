/-
`storeTxnRead__End` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `tr.End()` ends the read transaction at `tr` (the `RUnlock` of its reader and of `s.mu`):
the transaction's tokens are the caller's again (its reader's token is gone). -/
abbrev mvcc.storeTxnRead.End.spec : Prop :=
  ∀ (tr s trace ti : Loc) (rt : GoInterfaceOk) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeTxnReadIs tr s rt trace γ log rev ∗ mvcc.txReader rt log ∗
      s.[store, go!"kvindex"] ↦□ (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      sync.ownRWMutexRLocked (mvcc.muAddr s) mvcc.muInv ∗
      sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s γ) ∗ mvcc.idxReader ti γ.idx }}
    (App (Val (tr @!! go.GoType.PointerType storeTxnRead.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ }}

end spec

end EtcdGrove
end Perennial
