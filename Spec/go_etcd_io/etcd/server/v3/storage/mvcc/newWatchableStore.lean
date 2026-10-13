/-
`newWatchableStore` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`, `Spec/.../NewStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

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

/-- `newWatchableStore(lg, b, le, cfg)` on a fresh backend (`NewStore`'s premises: the backend's
contract at any of the store's names with the bucket `γb`, the empty bucket's view, the lessor):
a watchable store (`isWatchableStore`: the inner store with its read view pointed at the
watchable store, the lock's guard with its invariant at the initial log `[[], []]`, no watcher,
the victims' wake-up channel, the stop channel), the post-lock hook recorded, the sole writer at
the initial log (`watchWriter`: the certificate, every revision token and its half of the
notified log), every watch token (`watchToks`: a registration costs one), every reader slot of the two stores' locks (`watchReader`), the right to close the
stop channel (`stopCloser`) and the inner store (`storeCloser`), and the zero wait group (for
`New`). The lessor's `SetRangeDeleter` takes the deleter closure as an opaque value (its later
calls of it are outside the model, as in `NewStore`). -/
abbrev mvcc.newWatchableStore.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (γb γl : GName) (P : IProp GF) (f : val),
  0 ≤ sint.Z cfg.CompactionBatchLimit' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb⌝ →
        mvcc.isKeyBackend b (mvcc.bucketView γ) (mvcc.delKey γ) (mvcc.writerRes s γ) P f) ∗
      ghostMapAuth γb 1 (∅ : mvcc.Bucket) ∗ mvcc.isLessor le γl }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl⌝ ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.hookIs γ.st P f ∗ mvcc.watchWriter γ [[], []] ∗
      mvcc.watchToks γ (2 ^ 63 - 3) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.watchReader s st γ) ∗
      (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc) ∗
      mvcc.storeCloser st ∗
      typedPointsto (mvcc.wsWgAddr s) (zero_val sync.WaitGroup) (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
