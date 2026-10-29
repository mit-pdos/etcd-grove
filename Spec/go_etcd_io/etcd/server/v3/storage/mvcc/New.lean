/-
`New` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

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

/-- `New(lg, b, le, cfg)` on a fresh backend (`newWatchableStore`'s premises): the watchable store
as a `WatchableKV`, its two loops started (`s.wg.Add(2)`, each with a reader slot and a done
token), with what `newWatchableStore` gives (every watch token among it) but those two slots, and the right to close it
(`wsCloser`: the stop channel's close, the wait for the loops, the inner store's close, with its
scheduler's stop token: D19m (C), 2026-10-18), on a backend that records no compaction
(`kbNoCmp`, `NewStore`'s: D19l (v) (A), D22 S-g). The
index's names `γi` and the certificate map's `γok` are the caller's, fresh, and the map's
authority is handed back (2026-10-16, D13a: the etcd server chooses them before `newRaftNode`,
and its KV certificates' invariant, `kvCertInv`, takes the authority). -/
abbrev mvcc.New.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (γi : mvcc.IdxNames) (γok γtag : GName),
  mvcc.batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb⌝ → mvcc.storeBackend b s γ P) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbNoCmp kb γb ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStore.ty) #s);
      ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧ γ.st.kb = kb ∧
        γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag⌝ ∗
        mvcc.isWatchableStore s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd s st γ) ∗ mvcc.hookInit γ.st P f ∗ mvcc.watchWriter γ [[], []] ∗
        mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 2) (),
          mvcc.watchReader s st γ) ∗
        mvcc.wsCloser s st γ.st ∗ mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st 0 }}

end spec

end EtcdGrove
end Perennial
