/-
`NewStore` (`kvstore.go`), on a fresh backend. Lean-first (no Rocq counterpart); see
`InvStore.lean`.
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
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`NewStore` at the mode `aq`** (mvcc's candidate API, `notes/mvcc-api-proof-plan.md`, stage
P2): the store in the abstract mode
when `aq`: the caller gets the writer's fragment without the old mode's gate (`writerFragA`) and
the client's halves of the abstract committed log and of the pending revision. -/
abbrev mvcc.NewStore.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (wq : Bool) (γi : mvcc.IdxNames) (γok : GName)
    (aq : Bool),
  mvcc.batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb ∧ γ.idx = γi⌝ →
        mvcc.storeBackend b s γ P) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbNoCmp kb γb ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      mvcc.kbSRM kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
      ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = kb ∧ γ.watchQ = wq ∧ γ.idx = γi ∧ γ.cok = γok ∧
        γ.cm = decide (mvcc.kbCmpM kb) ∧ γ.absQ = aq⌝ ∗
      mvcc.isStore s γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd) ∗ ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗ mvcc.hookInit γ P f ∗
      (∃ rv wv : Loc,
        s.[store, go!"ReadView"] ↦
          (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
        mvcc.isReadView rv s γ ∗
        s.[store, go!"WriteView"] ↦
          (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
        mvcc.isWriteView wv s γ) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd kb) (),
        mvcc.storeReaderC s γ) ∗
      ownToks γ.revs (2 ^ 63 - 5) ∗ mvcc.idxCert γ.idx [[], []] ∗
      (if wq then mvcc.logQ γ [[], []] else iprop(True)) ∗ mvcc.storeCloser s γ ∗
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      (if aq then iprop(mvcc.writerFragA γ ∗ ghostVar γ.abs (1 : Qp).half ([[], []] : mvcc.Log) ∗
          ghostVar γ.pnd (1 : Qp).half (none : Option (List mvcc.Change)))
       else mvcc.writerFrag γ) ∗
      mvcc.crevUB γ.idx (1 : Qp).half (-1) ∗ mvcc.retiredAt γ (mvcc.nJobRd kb) }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `NewStore(lg, b, le, cfg)` over a fresh real backend `d` (what its creator holds, as `NewStore_backend` takes it:
the backend boundary is unchanged in this candidate), the write-backs paid from time receipts
(`□ (⧗ 1 ={⊤}=∗ backend.wbTok d.γB)`, so that no write takes a token), the real lessor (today's
`isLessor`), and a batch limit not negative; the threads bound the store's readers
(`threadBound GF ≤ 2 ^ 30`: Go's read-write mutexes allow `2 ^ 30` readers), at the mode `wq` its caller chooses (whether
the store will have watchers: `New` wraps it in a watchable store; a plain store's caller, `false`):
a store `s` of a new store `γ` at `mvccStart`, its backend's identity, its whole open token;
without watchers, the range deleter it set on the lessor; with watchers, the lessor's deleter slot
and the right to wrap the store (the watchable store sets its own deleter and views). -/
abbrev mvcc.NewStore.specC : Prop :=
  ∀ (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (d : mvcc.KBReal) (Pk : IProp GF)
    (γl : GName) (rd0 : GoFunc) (wq : Bool),
  0 ≤ sint.Z cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 → threadBound GF ≤ 2 ^ 30 →
  mvcc.bridgeParams d.P →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ∗
      mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
      □ (⧗ 1 ={⊤}=∗ backend.wbTok d.γB) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.bkRTx d.γB d.P d.be) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
      (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s;
      ∃ γ : mvcc.MvccName, ⌜mvcc.mvccLeases γ = γl ∧ mvcc.mvccBackend γ = d.γB ∧ mvcc.mvccWatched γ = wq⌝ ∗
        mvcc.isMvcc s γ ∗ mvcc.mvccState γ mvcc.mvccStart ∗ mvcc.mvccBackendIs γ d.P Pk d.be ∗
        mvcc.mvccOpen γ 1 ∗
        (if wq then iprop((∃ rd : GoFunc, lease.rdOwn γl rd) ∗ mvcc.mvccWrapRight γ s)
         else iprop(∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.mvccDeleter rd γ)) }}

end spec

end EtcdGrove
end Perennial
