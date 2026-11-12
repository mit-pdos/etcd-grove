/-
`New` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
-/
module

public import Spec.go_uber_org.zap.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RdCalls
public import Perennial.ProgramLogic.Bounds
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStoreSess
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WsCloserR

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

/-- **`New(lg, b, le, cfg)` over a real backend `d` holding the image of `L' = [[], []] ++ R` at the
records `r`** (B3; mvccfull's Freeze, 2026-11-10). The pre is `newWatchableStore.spec`'s; the post the fresh spec's with
the right to close by the mode at the restored revision (`wsCloser s st γ.st ∗ crevRightM γ.st` →
`wsCloserM s st γ.st r.crev`: on, `wsCloserR`, the inner store's restorable compaction right, with
the resumed job if any; off, `wsCloser`), the API's client parts at `L'` and `r.crev`, the map at
`M`, `hookP` (no `f`), and `newWatchableStore`'s additions (the lessor's owner part at
`pendItems L' []`, `resumeBackM`). The loops (`syncWatchersLoop`, `syncVictimsLoop`) start as
today: with no watcher they do nothing of the log.

**The fresh spec** (until the Freeze; its statement at commit `ae30739dde`), whose clauses
the above changes: `New(lg, b, le, cfg)` on a fresh backend (`newWatchableStore`'s premises): the watchable store
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
write-back supply. (C3's store law, 2026-11-02) The store's compaction permit is the caller's
`Perm` (`crevPermIs`). (Track A, `New.spec`, 2026-11-06) As `newWatchableStore`: the write
resource's registration, the API's client parts (`newClient` at half) and a later credit.
(the backend-auth-split stage, 2026-11-02) The backend's reader tokens it takes are the backend's
counted stock less the opener's two (`nReaders`, past the backend's pool), the readers it gives counted from it;
until then all `actualMaxReaders` of them. -/
abbrev mvcc.New.spec : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (b le : GoInterface) (cfg : StoreConfig)
    (d : mvcc.KBReal) (γb γl : GName) (P : IProp GF) (rd0 : GoFunc)
    (γi : mvcc.IdxNames) (γok γtag : GName) (M : GMap w64 mvcc.Log) (Perm : Int → IProp GF)
    (R : mvcc.Log) (r : mvcc.CmpRecs) (Ls : List w64)
    (hk : Option val) (Pre Q Post X Y : IProp GF) (dq : DFrac),
  {{ ⌜mvcc.batchLimitOk cfg.CompactionBatchLimit' ∧ mvcc.restoreLogOk R⌝ ∗
      -- (premise fixes 6) the logger nil (replaced by `zap.NewNop()`) or a zap logger
      zapLoggerOrNil lg ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.storeSessT b s γ P) ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.restoreFixM d γ -∗ mvcc.storeBackendTR b s γ P r) ∗
      (∀ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.keyCleanReadR b (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d)
          (mvcc.kbRecs γ.kb γ.bucket r) r) ∗ mvcc.restoreRegM d ∗
      mvcc.restoreImageM d γb ([[], []] ++ R) r ∗ mvcc.restoreRcptM d ([[], []] ++ R) ∗
      mvcc.kbNoDelOff (some d) ∗ mvcc.kbRegRight (some d) ∗
      mvcc.kbWT (some d) ∗ mvcc.kbWT (some d) ∗ mvcc.kbSRM (some d) ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d)) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      lease.leaseOwn γl Ls ∅ ∗
      ⌜∀ it lid, (mvcc.pendItems ([[], []] ++ R) []).lookup it = some lid →
        lid ∈ Ls ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 M ∗
      (⌜([[], []] ++ R).length ≤ 2⌝ ∨ (W64 (([[], []] ++ R).length : Int)) ↪[γok]□ ([[], []] ++ R) ∨
        (W64 0) ↪[γok]□ ([] : mvcc.Log)) ∗
      (⌜r.finRev = -1⌝ ∨ □ Perm r.finRev) ∗ (⌜r.crev = -1⌝ ∨ □ Perm r.crev) ∗
      mvcc.resumeCtxM d r P hk Pre Q Post dq X Y ∗
      (if r.resumes then mvcc.kbWTSupplyM (some d) else iprop(True)) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStore.ty) #s);
      ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧
        γ.st.kb = some d ∧ γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag ∧ γ.st.cm = d.cm⌝ ∗
        mvcc.isWatchableStore s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd s st γ ∗
          mvcc.rdCalls rd (go.GoType.PointerType watchableStore.ty) #s) ∗ mvcc.hookP γ.st P ∗
        mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 M ∗
        ([∗list] _x ∈ List.replicate (mvcc.nReaders - mvcc.nJobRd (some d) - 2) (),
          mvcc.watchReader s st γ) ∗
        mvcc.wsCloserM s st γ.st r.crev ∗
        mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st (mvcc.nJobRd (some d)) ∗
        mvcc.crevPermIs γ.st Perm ∗
        mvcc.writerReg st γ.st ∗
        mvcc.api.newClient γ.st.api ([[], []] ++ R) r.crev (1 : Qp).half st ∗
        lease.leaseOwn γl Ls (mvcc.pendItems ([[], []] ++ R) []) ∗
        mvcc.resumeBackM d r hk dq Post Y ∗ £ 1 }}

end spec

end EtcdGrove
end Perennial
