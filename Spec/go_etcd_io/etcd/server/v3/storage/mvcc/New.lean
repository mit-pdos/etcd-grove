/-
`New` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RdCode
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

/-- `New(lg, b, le, cfg)` on a fresh backend (`newWatchableStore`'s premises): the watchable store
as a `WatchableKV`, its two loops started (`s.wg.Add(2)`, each with a reader slot and a done
token), with what `newWatchableStore` gives (every watch token among it) but those two slots, and the right to close it
(`wsCloser`: the stop channel's close, the wait for the loops, the inner store's close, with its
scheduler's stop token: D19m (C), 2026-10-18), on a backend that records no compaction
(`kbNoCmp`, `NewStore`'s: D19l (v) (A), D22 S-g). The
index's names `γi` and the certificate map's `γok` are the caller's, fresh, and the map's
authority is handed back (2026-10-16, D13a: the etcd server chooses them before `newRaftNode`,
and its KV certificates' invariant, `kvCertInv`, takes the authority). (M2, the storage side, P3,
2026-10-30) As `newWatchableStore`: the frozen fact by the mode, the compaction right's half of the
revision's authority beside the closer in compaction mode (`crevRightM γ.st`: the caller makes
the compaction right of it only after its last error return, Go's deferred `kv.Close()`, or
freezes the store and watches, `noCompactor_of_new`), the logical mode the instance's, and no
write-back supply. -/
abbrev mvcc.New.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (γi : mvcc.IdxNames) (γok γtag : GName),
  mvcc.batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb ∧ γ.idx = γi⌝ →
        mvcc.storeBackend b s γ P) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbNoCmp kb γb ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      mvcc.kbSRM kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStore.ty) #s);
      ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧ γ.st.kb = kb ∧
        γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag ∧ γ.st.cm = decide (mvcc.kbCmpM kb)⌝ ∗
        mvcc.isWatchableStore s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd s st γ) ∗ mvcc.hookInit γ.st P f ∗ mvcc.watchWriter γ [[], []] ∗
        mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd kb - 2) (),
          mvcc.watchReader s st γ) ∗
        mvcc.wsCloser s st γ.st ∗ mvcc.crevRightM γ.st ∗
        mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st (mvcc.nJobRd kb) }}

/-- **`New` at the mode `aq`** (mvcc's candidate API, `notes/mvcc-api-proof-plan.md`): `spec`'s
(this at `aq = false`, `New.wp_proof`), the store in the abstract mode when `aq` (`newWatchableStore`'s
abstract parts). -/
abbrev mvcc.New.specA : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (γi : mvcc.IdxNames) (γok γtag : GName) (aq : Bool),
  mvcc.batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb ∧ γ.idx = γi⌝ →
        mvcc.storeBackend b s γ P) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbNoCmp kb γb ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      mvcc.kbSRM kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStore.ty) #s);
      ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧ γ.st.kb = kb ∧
        γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag ∧ γ.st.cm = decide (mvcc.kbCmpM kb) ∧
        γ.st.absQ = aq⌝ ∗
        mvcc.isWatchableStore s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗
          (if aq then mvcc.rdCode rd s else mvcc.rdIs rd s st γ)) ∗ mvcc.hookInit γ.st P f ∗ mvcc.watchWriter γ [[], []] ∗
        mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd kb - 2) (),
          mvcc.watchReader s st γ) ∗
        mvcc.wsCloser s st γ.st ∗ mvcc.crevRightM γ.st ∗
        (if aq then iprop(mvcc.writerFragA γ.st ∗ ghostVar γ.st.abs (1 : Qp).half ([[], []] : mvcc.Log) ∗
          ghostVar γ.st.pnd (1 : Qp).half (none : Option (List mvcc.Change)))
         else mvcc.writerFrag γ.st) ∗ mvcc.retiredAt γ.st (mvcc.nJobRd kb) }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `New(lg, b, le, cfg)` over a fresh real backend `d` (what its creator holds, as `NewStore_backend` takes it:
the backend boundary is unchanged in this candidate), the write-backs paid from time receipts
(`□ (⧗ 1 ={⊤}=∗ backend.wbTok d.γB)`, so that no write takes a token), the real lessor (today's
`isLessor`), and a batch limit not negative; the threads bound the store's readers
(`threadBound GF ≤ 2 ^ 30`: Go's read-write mutexes allow `2 ^ 30` readers): the watchable store `ws` of a new store `γ` at
`mvccStart`, with watchers, its backend's identity (the batch lock's invariant `Pk`), its whole
open token, and the range deleter it set on the lessor (its own `Write`). -/
abbrev mvcc.New.specC : Prop :=
  ∀ (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (d : mvcc.KBReal) (Pk : IProp GF)
    (γl : GName) (rd0 : GoFunc),
  mvcc.batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  threadBound GF + 2 ≤ 2 ^ 30 → mvcc.bridgeParams d.P → d.cm = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ∗
      mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
      backend.dlInit d.γB ∗ backend.wbTok d.γB ∗ backend.wbTok d.γB ∗
      □ (⧗ 1 ={⊤}=∗ backend.wbTok d.γB) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.bkRTx d.γB d.P d.be) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
      (Val #le)) (Val #cfg))
  {{ (ws : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStore.ty) #ws);
      ∃ γ : mvcc.MvccName, ⌜mvcc.mvccLeases γ = γl ∧ mvcc.mvccBackend γ = d.γB⌝ ∗
        mvcc.isWatchableMvcc ws γ ∗ mvcc.mvccState γ mvcc.mvccStart ∗
        mvcc.mvccBackendIs γ d.P Pk d.be ∗ mvcc.mvccOpen γ 1 ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.mvccDeleter rd γ) }}

end spec

end EtcdGrove
end Perennial
