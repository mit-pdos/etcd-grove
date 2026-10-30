/-
**M2, the storage side, step 2: the compaction chain over the restorable right (Draft)**
(`notes/m2-storage-plan.md`, "After review round 4": round 4's S3, the texts approval items 4/17,
24 and the resumed compaction's lock, A2). Imported by nothing; no `axiom`, no `sorry`; nothing
switched.

Round 3 left these as prose patches over step 1's Supply texts (`store.Compact.specD` with
`storeStop s γ ∗ compactRight γ c`): here they are Lean, so that one text is approved.
- **`compactJobPreR`**: `compactJobPreD` with the jobs' share at fixed objects
  (`∃ o, storeStopR s γ o`) in place of `storeStop s γ ∗ schedLive γ.sch` (Q6: no `schedLive`, the
  barriers tracked).
- **`store.Compact.specR`** (item 17, export `mvcc_store_Compact`): `compactRightR s γ c` in place of
  `storeStop s γ ∗ compactRight γ c`, in the pre and the three post arms.
- **`updateCompactRev.specR`, `compactLockfree.specR`** (internal): the same, and the critical
  section's context by the hook's state (`lockCtxM`, A2): the hook set (today's `hookIs ∗
  csContract`), or unset (`restore()`'s resumed compaction inside `Restore`, before the server sets
  the new backend's hook: the batch lock's invariant passes through, `lockNilSpec`).
- **`mvcc_NewStore_backend_cmpR`** (item 24, proved over `NewStore.specD`): the post's
  `compactRight γ (-1) ∗ storeStop s γ` becomes `compactRightR s γ (-1)` (`compactRightR_of_closer`
  in place of the discarding `compactRight_of_closer`).

The chain's proofs over them (`scheduleCompaction`, `compactBarrier`, `compact`, `updateCompactRev`
with the tracked barrier; Supply's copies over `storeStop`) are the switch's: what changes is each
read of the fields through `storeStopR`'s invariant (an atomic load, the job holding the run token)
and the `None` arm of `lockCtxM` through `lockNilSpec`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.StoreBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftRestore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **Draft of `compactJobPre`, step 2** (persistent): `compactJobPreD` with the jobs' share of the
fields at fixed objects (`storeStopR`) in place of `storeStop s γ ∗ schedLive γ.sch`. -/
def mvcc.compactJobPreR (s : Loc) (γ : mvcc.StoreNames) (rev : w64) : IProp GF :=
  iprop(mvcc.isStore s γ ∗ (∃ o : mvcc.StoreObjs, mvcc.storeStopR s γ o) ∗ ⌜mvcc.storeCmp γ⌝ ∗
    mvcc.crevLb γ.idx (sint.Z rev) ∗ mvcc.kbWTSupplyM γ.kb ∗
    ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ mvcc.idxNevLb γ.idx log ∗
      ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝)

instance mvcc.compactJobPreR_persistent (s : Loc) (γ : mvcc.StoreNames) (rev : w64) :
    Persistent (mvcc.compactJobPreR (GF := GF) s γ rev) := by
  unfold mvcc.compactJobPreR; infer_instance

/-- **The critical section's context, by the hook's state** (draft, A2): the hook set to `f`
(today's: the writer's hook and the caller's contract for it), or unset (`none`: the batch lock's
invariant `P` named, the writer's fragment, the new backend's unset hook lent, and the caller's
update from `Pre` to `Post`, `LockInsideApply` running nothing: `lockNilSpec`). -/
def mvcc.lockCtxM (γ : mvcc.StoreNames) (P : IProp GF) (hk : Option val) (Pre Q Post : IProp GF) :
    IProp GF :=
  match hk with
  | some f => iprop(mvcc.hookIs γ P f ∗ mvcc.csContract P f Pre Q Post)
  | none => iprop(mvcc.hookP γ P ∗ mvcc.writerFrag γ ∗ mvcc.kbHookNil γ.kb ∗ Pre ∗ (Pre ={⊤}=∗ Post))

/-- What the call gives back of the context (with `Post` or `Pre` beside it). -/
def mvcc.lockBackM (γ : mvcc.StoreNames) (P : IProp GF) (hk : Option val) : IProp GF :=
  match hk with
  | some f => mvcc.hookIs γ P f
  | none => iprop(mvcc.hookP γ P ∗ mvcc.writerFrag γ ∗ mvcc.kbHookNil γ.kb)

/-- **Draft of `store.Compact.spec`, step 2** (item 17 with item 4's supply line; export
`mvcc_store_Compact`): `store.Compact.specD`'s text with the restorable right `compactRightR s γ c`
in place of `storeStop s γ ∗ compactRight γ c` (the pre) and of `compactRight γ _` (the post's three
arms). The caller (the apply thread) always has the hook set. -/
abbrev mvcc.store.Compact.specR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : mvcc.Log) (te : Bool),
  trace ≠ null → mvcc.storeCmp γ → -1 ≤ c →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.compactRightR s γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.hookIs γ P f ∗
      mvcc.csContract P f Pre Q Post ∗ traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗
      mvcc.kbWTSupplyM γ.kb }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Compact")) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); traceutil.ownTrace trace te ∗
      mvcc.storeRT γ ∗ mvcc.hookIs γ P f ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.compactRightR s γ (sint.Z rev) ∗
        mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗ mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        (∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜(log.length : Int) ≤ sint.Z rev⌝) ∗
        mvcc.compactRightR s γ c ∗ Pre)) }}

/-- **Draft of `store.updateCompactRev.spec`, step 2**: `updateCompactRev.specD` with the restorable
right, the job premise `compactJobPreR`, and the critical section's context by the hook's state
(`lockCtxM`: `restore()`'s resumed call has it unset). -/
abbrev mvcc.store.updateCompactRev.specR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c : Int) (P : IProp GF) (hk : Option val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.lockCtxM γ P hk Pre Q Post ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"updateCompactRev")) (Val #rev))
  {{ (ch : GoChan) (prev : w64) (err : GoInterface), RET (PairV (PairV #ch #prev) #err);
      mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk ∗
      ((⌜err = GoInterface.nil ∧ ch = chan.nil ∧ prev = W64 c ∧ c < sint.Z rev⌝ ∗
        mvcc.muInvAt s γ 1 (sint.Z rev) ∗ mvcc.compactRightR s γ (sint.Z rev) ∗ Post ∗
        mvcc.compactJobPreR s γ rev) ∨
      (⌜sint.Z rev ≤ c ∧ prev = W64 0⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil ∧ prev = W64 0⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        (∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜(log.length : Int) ≤ sint.Z rev⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre)) }}

/-- **Draft of `store.compactLockfree.spec`, step 2**: `compactLockfree.specD` likewise (what
`restore()` calls for the compaction it resumes: `resumeK`, at `hk = none`). -/
abbrev mvcc.store.compactLockfree.specR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c : Int) (P : IProp GF) (hk : Option val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.lockCtxM γ P hk Pre Q Post ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactLockfree")) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.muInvAt s γ 1 (sint.Z rev) ∗
        mvcc.compactRightR s γ (sint.Z rev) ∗ mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗
        mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre)) }}

/-- **Draft of the export `mvcc_NewStore_backend_cmp`, step 2** (item 24; proved over
`NewStore.specD`, a hypothesis here, linked at the switch): the post's
`compactRight γ (-1) ∗ storeStop s γ` is the restorable right `compactRightR s γ (-1)` (the closer
split, not discarded: `compactRightR_of_closer`). -/
theorem mvcc_NewStore_backend_cmpR [go_etcd_io.etcd.cache.v3.Assumptions]
    (hNS : mvcc.NewStore.spec (GF := GF) (hG := hG)) (lg : Loc) (le : GoInterface)
    (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (hcm : d.cm = true) (γb γl : GName)
    (Pk : IProp GF) (f : GoFunc) (hf : f ≠ func.nil) (rd0 : GoFunc)
    (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit') (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ backend.plHookRO d.γB f ∗
        mvcc.keySized d.γB d.P d.be ∗ backend.dlInit d.γB ∗ backend.fkV d.γB true ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
        backend.wbTok d.γB ∗ backend.wbTok d.γB ∗ mvcc.kbSRM (some d) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #le)) (Val #cfg))
    {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
        ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d ∧ γ.watchQ = false ∧ mvcc.storeCmp γ⌝ ∗
        mvcc.isStore s γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd) ∗
        ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗ mvcc.hookIs γ Pk #f ∗
        (∃ rv wv : Loc,
          s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv s γ ∗
          s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"WriteView"] ↦
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.writeView.ty) #wv : GoInterface) ∗
          mvcc.isWriteView wv s γ) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (),
          mvcc.storeReaderC s γ) ∗
        ownToks γ.revs (2 ^ 63 - 5) ∗ mvcc.idxCert γ.idx [[], []] ∗
        mvcc.compactRightR s γ (-1) ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗
        mvcc.retiredAt γ 1 }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hhk, #Hsz, Hdl, #Hfk, Hv, Hncmp, Hrg, Hw1, Hw2, Hsrm,
    Hrts, Hlrd, #Hle, Hro⟩ HΦ
  iapply wp_fupd
  wp_apply (mvcc.NewStore_backend hNS backend.backend.wp_ConcurrentReadTx
        backend.backend.wp_ReadTx backend.backend.wp_BatchTx backend.backend.wp_ForceCommit
        backend.backend.wp_Size backend.backend.wp_SizeInUse
        backend.concurrentReadTx.wp_RLock backend.concurrentReadTx.wp_RUnlock
        backend.concurrentReadTx.wp_UnsafeRange backend.readTx.wp_RLock backend.readTx.wp_RUnlock
        backend.readTx.wp_UnsafeRange backend.batchTxBuffered.wp_LockInsideApply
        backend.batchTxBuffered.wp_LockOutsideApply backend.batchTxBuffered.wp_UnsafeSeqPut
        backend.batchTxBuffered.wp_Unlock backend.batchTxBuffered.wp_UnsafeRange
        backend.batchTxBuffered.wp_UnsafeCreateBucket
        backend.batchTxBuffered.wp_UnsafeDelete schema.bucket.wp_ID schema.bucket.wp_Name
        schema.bucket.wp_IsSafeRangeBucket backend.backend.wp_LockForSafeRangeDelete
        backend.backend.wp_UnlockForSafeRangeDelete backend.batchTxBuffered.wp_UnsafePut
        lg le cfg d hP γb γl Pk f hf rd0 hcfg hrb)
      $$ [Hdl Hv Hncmp Hrg Hw1 Hw2 Hsrm Hrts Hlrd Hro]
    as %s ⟨%γ, %Hγ, #Hst, Hrd, Hcok, Hhk', Hviews, Hrds, Htoks, #Hc, Hcl, Hfs, Hright, Hret⟩
  · iframe #; iframe Hdl Hv Hncmp Hrg Hw1 Hw2 Hsrm Hrts Hlrd Hro
    iintro !> %_; itrivial
  have hj : mvcc.nJobRd (some d) = 1 := by unfold mvcc.nJobRd; simp [hcm]
  rw [hj]
  imod mvcc.compactRightR_of_closer s γ ⊤ $$ Hcl Hright with Hcr
  imodintro
  iapply HΦ
  iexists γ
  isplitr
  · ipureintro
    refine ⟨Hγ.1, Hγ.2.1, Hγ.2.2.1, Hγ.2.2.2, ?_⟩
    show mvcc.kbCmpM γ.kb
    rw [Hγ.2.2.1]; exact hcm
  iframe Hrd Hcok Hhk' Hviews Hrds Htoks Hcr Hfs Hret
  iframe #

end draft

end EtcdGrove
end Perennial
