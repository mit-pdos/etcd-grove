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
`New`). The backend records no compaction (`kbNoCmp`, `NewStore`'s; D19l (v) (A), D22 S-g), and the inner store's closer holds its scheduler's stop token (D19m (C), 2026-10-18). The lessor's `SetRangeDeleter` takes the deleter closure as an opaque value (its later
calls of it are outside the model, as in `NewStore`). The index's names `γi` and the
certificate map's `γok` are the caller's, fresh, and the map's authority is handed back
(2026-10-16, D13a: the etcd server chooses them before `newRaftNode`, and its KV certificates'
invariant takes the authority). -/
abbrev mvcc.newWatchableStore.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (γi : mvcc.IdxNames) (γok γtag : GName),
  0 ≤ sint.Z cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb⌝ → mvcc.storeBackend b s γ P) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbNoCmp kb γb ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧ γ.st.kb = kb ∧
        γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag⌝ ∗
      mvcc.isWatchableStore s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd) ∗ mvcc.hookInit γ.st P f ∗ mvcc.watchWriter γ [[], []] ∗
      mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.watchReader s st γ) ∗
      (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc) ∗
      mvcc.storeCloser st γ.st ∗ mvcc.writerFrag γ.st ∗
      typedPointsto (mvcc.wsWgAddr s) (zero_val sync.WaitGroup) (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
