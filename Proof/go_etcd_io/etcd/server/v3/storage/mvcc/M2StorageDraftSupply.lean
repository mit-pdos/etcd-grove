/-
**M2, the storage side: Q1 (a), the write-back supply per compaction** (`notes/m2-storage-plan.md`,
"Q1 (a), drafted"; the user's answer, 2026-10-30). Draft statements and their proofs, imported by
nothing: each `…D` is what an existing definition or spec becomes at the switch, written in full;
nothing is switched, nothing assumed (no `axiom`, no `sorry`).

The compaction's write-back supply (`kbWTSupplyM γ.kb`, persistent) leaves the store's creation
(`NewStore`/`newWatchableStore`/`New`, and the exports `mvcc_NewStore_backend(_cmp)`) and the store's
state (`physCmp`), and is taken by the compaction instead: `store.Compact`'s pre (and its callees
`compactLockfree`'s and `updateCompactRev`'s), which hands it on to the job in the job's persistent
premise (`compactJobPre`), where `scheduleCompaction` finds it. At `cm = false` it is `True`
(`cmOff_res`), and `store.Compact` is not callable there anyway (`storeCmp γ`).

What is proved here, against the drafted statements:
- **the compaction chain, linked**: `updateCompactRev`, `compactLockfree`, `Compact`, `compact` and
  `scheduleCompaction`, each a copy of today's proof against its `specD` (the changes: the supply
  from the pre or from `compactJobPreD`, the store's facts read only through `physCmpD`, the
  destructuring patterns), and `mvcc_store_CompactD : store.Compact.specD` with today's linked
  callees, no hypothesis;
- **the creation side, the changed steps**: `physCmp_allocD` (`NewStore`'s one changed step: the
  compaction facts without the supply), the bridge `NewStore_backendD` over `NewStore.specD`, and
  the exports `mvcc_NewStore_backendD`/`_cmpD` over `NewStore.specD` (a hypothesis: `NewStore`'s own
  proof builds `isStore`, whose `physOk` holds `physCmp`, so it changes only with the in-place
  redefinition of `physCmp`; its one changed step is `physCmp_allocD`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.StoreBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Link
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

/-! ## The supply and the store's compaction facts -/

instance mvcc.kbWTSupplyM_persistent (kb : Option mvcc.KBReal) :
    Persistent (mvcc.kbWTSupplyM (GF := GF) kb) := by
  unfold mvcc.kbWTSupplyM; split <;> infer_instance

/-- A compacting store's supply. -/
theorem mvcc.kbWTSupplyM_on (kb : Option mvcc.KBReal) (h : mvcc.kbCmpM kb) :
    mvcc.kbWTSupplyM (GF := GF) kb ⊣⊢ mvcc.kbWTSupply kb := by
  unfold mvcc.kbWTSupplyM; simp only [h, ↓reduceIte]; exact .rfl

/-- **Draft of `physCmp`** (redefined in place at the switch): the write right's invariant and the
store's registration, without the write-back supply (`compactJobPreD` carries it). -/
def mvcc.physCmpD (s : Loc) (γ : mvcc.StoreNames) : IProp GF :=
  if mvcc.kbCmpM γ.kb then iprop(mvcc.mwInv γ ∗ mvcc.storeRegd s γ) else iprop(True)

instance mvcc.physCmpD_persistent (s : Loc) (γ : mvcc.StoreNames) :
    Persistent (mvcc.physCmpD (GF := GF) s γ) := by
  unfold mvcc.physCmpD; split <;> infer_instance

/-- (draft of `physCmp_off`) -/
theorem mvcc.physCmpD_off (s : Loc) (γ : mvcc.StoreNames) (h : ¬ mvcc.kbCmpM γ.kb) :
    ⊢ mvcc.physCmpD (GF := GF) s γ := by
  unfold mvcc.physCmpD; simp only [h, ↓reduceIte]; iintro; itrivial

/-- (draft of `physCmp_on`) -/
theorem mvcc.physCmpD_on (s : Loc) (γ : mvcc.StoreNames) (h : mvcc.kbCmpM γ.kb) :
    mvcc.physCmpD (GF := GF) s γ ⊣⊢ iprop(mvcc.mwInv γ ∗ mvcc.storeRegd s γ) := by
  unfold mvcc.physCmpD; simp only [h, ↓reduceIte]; exact .rfl

/-- Today's facts give the drafted ones (what the proof copies below read the store's `physCmp`
through: they use nothing of it but `physCmpD`'s). -/
theorem mvcc.physCmpD_of_physCmp (s : Loc) (γ : mvcc.StoreNames) :
    mvcc.physCmp (GF := GF) s γ ⊢ mvcc.physCmpD s γ := by
  unfold mvcc.physCmp mvcc.physCmpD
  split
  · iintro ⟨#Hi, #Hr, -⟩; iframe Hi Hr
  · iintro -; itrivial

/-- **`NewStore`'s changed step** (draft of `physCmp_alloc`): the compaction facts from the key's
other half, the right and the registration, without the supply. -/
theorem mvcc.physCmp_allocD (s : Loc) (γ : mvcc.StoreNames) :
    mvcc.mwRest (GF := GF) γ ∗ mvcc.kbMW γ.kb γ.bucket ∗ mvcc.storeRegd s γ ={⊤}=∗
      mvcc.physCmpD s γ := by
  unfold mvcc.mwRest mvcc.physCmpD
  by_cases hc : mvcc.kbCmpM γ.kb
  · simp only [hc, ↓reduceIte]
    iintro ⟨Hh, Hmw, #Hr⟩
    imod (inv_alloc mvcc.mwN ⊤ iprop(∃ b : Bool, ghostVar γ.mwk (1 : Qp).half b ∗
        if b then mvcc.kbMW γ.kb γ.bucket else iprop(True))) $$ [Hh Hmw] with #Hi
    · inext
      iexists true
      iframe Hh
      simp only [↓reduceIte]
      iexact Hmw
    imodintro
    iunfold mvcc.mwInv
    iframe Hi Hr
  · simp only [hc, ↓reduceIte]
    iintro -; imodintro; itrivial

/-- (draft of `mwSwap_of_physOk`) -/
theorem mvcc.mwSwap_of_physCmpD (s : Loc) (γ : mvcc.StoreNames) (h : mvcc.kbCmpM γ.kb) :
    mvcc.physCmpD (GF := GF) s γ ⊢ mvcc.mwSwap (mvcc.storeW s γ) (mvcc.kbMW γ.kb γ.bucket) := by
  unfold mvcc.physCmpD
  simp only [h, ↓reduceIte]
  iintro ⟨#Hi, #Hr⟩
  iapply mvcc.mwSwap_frame (mvcc.writerRes s γ)
  isplitr
  · iintro !> HW
    ihave HW := mvcc.storeW_get s γ $$ [$Hr $HW]
    iframe HW
    iintro HW
    iapply mvcc.storeW_put s γ
    iframe Hr HW
  iapply mvcc.mwSwap_writerRes s γ h $$ Hi

/-- **Draft of `compactJobPre`** (redefined in place at the switch): today's, and the write-back
supply (`kbWTSupplyM γ.kb`), which `store.Compact`'s caller gave and the job's write sessions spend
(`scheduleCompaction`). -/
def mvcc.compactJobPreD (s : Loc) (γ : mvcc.StoreNames) (rev : w64) : IProp GF :=
  iprop(mvcc.isStore s γ ∗ mvcc.storeStop s γ ∗ schedule.schedLive γ.sch ∗ ⌜mvcc.storeCmp γ⌝ ∗
    mvcc.crevLb γ.idx (sint.Z rev) ∗ mvcc.kbWTSupplyM γ.kb ∗
    ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ mvcc.idxNevLb γ.idx log ∗
      ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝)

instance mvcc.compactJobPreD_persistent (s : Loc) (γ : mvcc.StoreNames) (rev : w64) :
    Persistent (mvcc.compactJobPreD (GF := GF) s γ rev) := by
  unfold mvcc.compactJobPreD; infer_instance

/-! ## The drafted compaction specs -/

/-- **Draft of `store.Compact.spec`** (Q1 (a); the full docstring it takes at the switch). **`s.Compact(trace, rev)`** with the compaction right at the store's compaction revision `c`
(`compactRight`: half the revision's authority and the compaction jobs' queue on the store's FIFO
scheduler, 2026-10-13, unit 5c; the caller is the one that compacts: the server's apply thread,
and the exclusive right serializes its compactions: the job is scheduled after `s.mu` is
released, so only the right can carry the queue there), under the critical-section
contract of the batch lock (`csContract`: `SetScheduledCompact`'s `LockInsideApply` runs the
post-lock hook), `trace ≠ nil`, the store's backend supporting the compaction (`storeCmp`: mvcc's
assumed backend, or a real backend in compaction mode, `KBReal.cm`: question 5's core stage, part
(4), 2026-10-29; until then the assumed backend only); under `s.mu` held exclusively (no transaction open):
* `rev > c`, `rev` a revision of the committed log: the compaction revision is `rev` (the right
  at `rev`, its queue ending with the job's `Post`, a lower bound `crevLb γ rev` for every reader
  since), `nil`, the caller's `Post`, and the job's channel (`compactChan`: once closed, `compactDone s γ rev`: the index and the bucket
  compacted at `rev`, `finishedCompactRev = rev`, or the compaction interrupted by `Close`);
* `rev ≤ c`: `ErrCompacted`, the barrier's channel (closed once the jobs before it ran:
  nothing promised, `True`), `Pre` back;
* `rev` above the committed log's last revision (a certificate of a shorter log): `ErrFutureRev`,
  a `nil` channel, `Pre` back.
The right's revision is at least `-1` (`NewStore`'s; each success raises it: 2026-10-13, unit 5c,
contract correction: the counter `crevN` cannot tell a right below `-1` from one at `-1`, and
then a `rev` in `(c, -1]` is `ErrCompacted` without `rev ≤ c`). The configuration's batch limit
is positive (`isStore`: `NewStore` excludes a negative one,
`issues/etcd-compaction-negative-batch-limit.md`).

**The delete-then-put premise** (2026-10-13, unit 6a): the caller holds a certificate of a log
`log` with revision `rev` (so `rev` is not above the committed log: the `ErrFutureRev` case does
not arise from such a caller) whose revision `rev` does not delete a key and put it again
(`NoDelPutAt`): else the compaction deletes the key's live value and a later read `Fatal`s
(`issues/etcd-compaction-delete-then-put.md`). The store records it for the new compaction
revision (`crevSafe`, in `s.mu`'s resource) and the keys the job deletes carry it (`delKey`), which
is what makes the readers' specs hold of a compacted store (`rangeAnswers_not_del`).

**The physical bound** (item 8, 2026-10-17; not a premise since 2026-10-18, D19b): the log up to
`rev` has fewer than `2 ^ 62` changes (`CompactSmall`), so the job's count of deleted keys (an
`int`) never wraps and `dbCompactionKeysCounter.Add(float64(count))` gets a non-negative value;
the job derives it from the certificate's time-receipt bound (`CompactSmall_of_cert`).

**The reader's token** (question 5's switch, decision (i), 2026-10-29): the caller lends the store's
reader token `storeRT γ` (the apply thread's, from `writerOwn`) for `checkPrevCompactionCompleted`'s
`ReadTx`, and gets it back in every case.

**The writer's hook** (Probe P1, 2026-10-30): `hookIs γ P f` (the persistent `hookOk` and the
writer's fragment `writerFrag`) is given back in every case, so the caller can still write
(`store.Write`), compact again, or restore.

**The write-back supply** (Q1 (a), 2026-10-30; review round 1's S9): the caller gives the
compaction's supply `kbWTSupplyM γ.kb` (persistent: it pays nothing per call; the server's from
`srvWTPool` and the apply thread's frozen part of the backend's name, `kbWTSupplyM_of_srvBeOwnD`,
R2-7; another creator's from a stock of its own, `kbWTSupplyM_alloc`), which the store no longer
keeps; the job gets it in its premise. Under `storeCmp γ` the gate is always on, so it is the
supply itself; the `M` form is kept because both sources produce it.
-/
abbrev mvcc.store.Compact.specD : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : mvcc.Log) (te : Bool),
  trace ≠ null → mvcc.storeCmp γ → -1 ≤ c →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeStop s γ ∗ mvcc.compactRight γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.hookIs γ P f ∗
      mvcc.csContract P f Pre Q Post ∗ traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗
      mvcc.kbWTSupplyM γ.kb }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Compact")) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗ mvcc.hookIs γ P f ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.compactRight γ (sint.Z rev) ∗
        mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗ mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.compactRight γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        (∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜(log.length : Int) ≤ sint.Z rev⌝) ∗
        mvcc.compactRight γ c ∗ Pre)) }}

/-- **Draft of `store.updateCompactRev.spec`**: the pre gains `kbWTSupplyM γ.kb` (its two write
sessions' tokens, today from `physCmp`), and the post's job premise is `compactJobPreD` (with it). -/
abbrev mvcc.store.updateCompactRev.specD : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeStop s γ ∗ mvcc.muInvAt s γ 1 c ∗ mvcc.compactRight γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.hookIs γ P f ∗ mvcc.csContract P f Pre Q Post ∗ mvcc.storeRT γ ∗
      mvcc.kbWTSupplyM γ.kb }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"updateCompactRev")) (Val #rev))
  {{ (ch : GoChan) (prev : w64) (err : GoInterface), RET (PairV (PairV #ch #prev) #err);
      mvcc.storeRT γ ∗ mvcc.hookIs γ P f ∗
      ((⌜err = GoInterface.nil ∧ ch = chan.nil ∧ prev = W64 c ∧ c < sint.Z rev⌝ ∗
        mvcc.muInvAt s γ 1 (sint.Z rev) ∗ mvcc.compactRight γ (sint.Z rev) ∗ Post ∗
        mvcc.compactJobPreD s γ rev) ∨
      (⌜sint.Z rev ≤ c ∧ prev = W64 0⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRight γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil ∧ prev = W64 0⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        (∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜(log.length : Int) ≤ sint.Z rev⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRight γ c ∗ Pre)) }}

/-- **Draft of `store.compactLockfree.spec`**: the pre gains `kbWTSupplyM γ.kb` (for
`updateCompactRev`). -/
abbrev mvcc.store.compactLockfree.specD : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeStop s γ ∗ mvcc.muInvAt s γ 1 c ∗ mvcc.compactRight γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.hookIs γ P f ∗ mvcc.csContract P f Pre Q Post ∗ mvcc.storeRT γ ∗
      mvcc.kbWTSupplyM γ.kb }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactLockfree")) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); mvcc.storeRT γ ∗ mvcc.hookIs γ P f ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.muInvAt s γ 1 (sint.Z rev) ∗
        mvcc.compactRight γ (sint.Z rev) ∗ mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗
        mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRight γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRight γ c ∗ Pre)) }}

/-- **Draft of `store.compact.spec`**: its job premise is `compactJobPreD`. -/
abbrev mvcc.store.compact.specD : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev prev : w64) (pcc : Bool) (te : Bool),
  trace ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.compactJobPreD s γ rev ∗
      mvcc.compactQueue γ (sint.Z rev) ∗ traceutil.ownTrace trace te }}
    (App (App (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compact")) (Val #trace))
      (Val #rev)) (Val #prev)) (Val #pcc))
  {{ (ch : GoChan), RET #ch; mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev)) ∗
      mvcc.compactQueue γ (sint.Z rev) ∗ traceutil.ownTrace trace te }}

/-- **Draft of `store.scheduleCompaction.spec`**: its job premise is `compactJobPreD` (the job's
write sessions' supply in it). -/
abbrev mvcc.store.scheduleCompaction.specD : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev prev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.compactJobPreD s γ rev ∗
      mvcc.compactTok γ (sint.Z rev) }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"scheduleCompaction")) (Val #rev))
      (Val #prev))
  {{ (h : KeyValueHash) (err : GoInterface), RET (PairV #h #err);
      mvcc.idxCompactor γ.idx (sint.Z rev) ∗ mvcc.compactJobResM γ.kb ∗
      ((⌜err = GoInterface.nil⌝ ∗ mvcc.compactedAt γ (sint.Z rev)) ∨
        (mvcc.errorfIs err ∗ mvcc.storeStopped s)) }}

/-! ## The compaction's proofs, against the drafted specs (copies of today's; the changed lines
marked `Q1 (a)`) -/

theorem mvcc.store.updateCompactRev.wp_proofD
    (h0 : schedule.NewJob.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.compactBarrier.spec (GF := GF) (hG := hG))
    (h2 : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG))
    (h3 : mvcc.SetScheduledCompact.spec (GF := GF) (hG := hG)) :
    mvcc.store.updateCompactRev.specD (GF := GF) (hG := hG) := by
  intro s γ rev c P f Pre Q Post logc hcmp
  wp_start as ⟨#Hs, #Hstop, HmuA, Hright, #HcertC, %HndC, HhookC, Hcs, HRTok, #HsupM⟩
  icases (mvcc.hookIs_split γ P f).1 $$ HhookC with ⟨#HhookC, HwFrag⟩
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  -- the compaction's objects, the current ones for good (D22 receiver epochs, S5b: until then
  -- `isStore`'s, pinned)
  icases mvcc.storeStop_open s γ $$ Hstop with
    ⟨%b, %ti, %ssched, %sstop, #Hb, #Hidx, #Hsched, #Hstopc, #Hstopch, #Hrstd, #Hph, #Hcurd⟩
  iunfold mvcc.physOk at Hph
  iNamed Hph
  try simp only
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  -- (question 5's core stage) a receipt from `s.revMu.Lock`'s resolution, for `ForceCommit`'s
  -- write-back token
  wp_take_receipt as Hr2
  ipersist s
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$HrevMu] as ⟨Hwl, HR⟩
  wp_auto_lc 2
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hlc1 HR with HR
  icases mvcc.revMuInv_open_cur s γ _ _ _ _ $$ [HR Hrstd Hcurd] with ⟨HR, HrstR, -, -⟩
  · iframe HR Hrstd Hcurd
  iunfold mvcc.revMuBody at HR
  icases HR with ⟨%log, %ntok, %c', HR⟩
  iNamed HR
  iunfold mvcc.muInvAt at HmuA
  iNamed HmuA
  iunfold mvcc.compactRight at Hright
  icases Hright with ⟨Hcr, Hq, #Hlive⟩
  ihave %Hcc := mvcc.crevUB_agree γ.idx _ _ c' c Hc.1 HcM $$ Hcrev Hcr
  subst Hcc
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨%ecp, #Hcomp⟩, ⟨%ef, #Hfut⟩, -⟩
  ihave #Hschp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  ihave #Hfifo := HisSched
  ihave #Hfifo' := Hfifo
  iunfold schedule.isFifo at Hfifo'
  icases Hfifo' with ⟨%Hnn, -⟩
  wp_auto
  wp_if_destruct
  · -- `rev <= s.compactMainRev`: `ErrCompacted`, a barrier job
    wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %Hchcap, Hchown⟩
    imod alloc_broadcast_chan (E := ⊤) iprop(True) γch ch $$ Hch Hchown with Hbc
    ihave #Hbc0 := ownBroadcastChan_Unknown _ _ _ _ $$ Hbc
    (try wp_auto)
    ipersist ch
    wp_func_lits
    (try wp_auto)
    wp_apply h0 γ.sch _ _ iprop(mvcc.compactCloser ch iprop(True) ∗ □ iprop(True)) iprop(True) iprop(True)
      $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx' %cd' !> %Φj ⟨Hrun, ⟨Hcl', -⟩, -, #Hctx'⟩ HΦj
      wp_auto
      wp_apply (h1 s γ ctx' cd' ch iprop(True)) $$ [$Hcl']
      · iframe #
        isplitl []
        · iunfold mvcc.barrierCtx
          iright
          iexact Hctx'
        imodintro; itrivial
      (try wp_auto)
      iapply HΦj
      iframe Hrun
    cases ssched with
    | nil => exact absurd rfl Hnn
    | ok sci =>
      wp_auto
      wp_apply h2 sci γ.sch j iprop(mvcc.compactCloser ch iprop(True) ∗ □ iprop(True)) iprop(True)
          iprop(True) none $$ [Hbc] as -
      · iframe #
        isplitl [Hbc]
        · iunfold mvcc.compactCloser
          isplitl [Hbc]
          · iexists γch; iexact Hbc
          imodintro; itrivial
        simp only [schedule.schedPre]
        iframe #
        ipureintro; trivial
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev HrstR]
      · iframe #
        inext
        iapply mvcc.revMuInv_close; iframe HrstR; iunfold mvcc.revMuBody
        iexists log, ntok, c'
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨Hne, Hbudget, Hc⟩
      (try wp_auto)
      iapply HΦ
      iframe HRTok
      isplitl [HwFrag]
      · iapply (mvcc.hookIs_split γ P f).2; iframe HwFrag HhookC
      iright; ileft
      isplitr
      · ipureintro; exact ⟨by word, rfl⟩
      isplitr
      · iexists ecp; iframe Hcomp; ipureintro; rfl
      isplitl [HcmpM HcrevM]
      · iunfold mvcc.muInvAt; simp only [named]; iframe; iframe #; ipureintro; exact HcM
      isplitl [Hcr Hq]
      · iunfold mvcc.compactRight; iframe Hcr Hq Hlive
      isplitl [Hcs]
      · iunfold mvcc.csContract at Hcs; icases Hcs with ⟨HPre, -, -⟩; iexact HPre
      iunfold mvcc.compactChan
      iexists γch
      iexact Hbc0
  · ihave #Hcert' := Hcert
    iunfold mvcc.idxCert at Hcert'
    icases Hcert' with ⟨-, %Hwf, -⟩
    have hc : sint.Z (W64 c' : w64) = c' := by
      have := Hwf.2.1
      word
    rw [hc] at Hif
    have Hgt : c' < sint.Z rev := by omega
    have hlen0 : 0 < log.length := List.length_pos_iff.mpr Hne
    have hl : sint.Z (W64 ((log.length : Int) - 1) : w64) = (log.length : Int) - 1 := by
      have := Hwf.2.1
      word
    rw [hl]
    wp_if_destruct
    · -- `rev > s.currentRev`: `ErrFutureRev`
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev HrstR]
      · iframe #
        inext
        iapply mvcc.revMuInv_close; iframe HrstR; iunfold mvcc.revMuBody
        iexists log, ntok, c'
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨Hne, Hbudget, Hc⟩
      (try wp_auto)
      iapply HΦ
      iframe HRTok
      isplitl [HwFrag]
      · iapply (mvcc.hookIs_split γ P f).2; iframe HwFrag HhookC
      iright; iright
      isplitr
      · ipureintro; exact ⟨Hgt, rfl, rfl⟩
      isplitr
      · iexists ef; iframe Hfut; ipureintro; rfl
      isplitr
      · iexists log; iframe Hcert; ipureintro; omega
      isplitl [HcmpM HcrevM]
      · iunfold mvcc.muInvAt; simp only [named]; iframe; iframe #; ipureintro; exact HcM
      isplitl [Hcr Hq]
      · iunfold mvcc.compactRight; iframe Hcr Hq Hlive
      iunfold mvcc.csContract at Hcs; icases Hcs with ⟨HPre, -, -⟩; iexact HPre
    · -- `s.compactMainRev = rev`, under both locks: the field and the revision's authority
      have hrl : sint.Z rev < log.length := by omega
      ihave Hcmpf : (s.[store, go!"compactMainRev"] ↦ (W64 c' : w64) : IProp GF) $$ [Hcmp HcmpM]
      · rw [show (DFrac.own 1 : DFrac) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half from
          dfrac_own_half_half 1]
        iapply ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).2
        iframe
      wp_auto
      imod crevUB_raise γ.idx c' (sint.Z rev) (by omega) $$ Hcr HcrevM Hcrev
        with ⟨Hcr, HcrevM, Hcrev, #Hlb⟩
      have hrw : (W64 (sint.Z rev) : w64) = rev := by word
      ihave Hcmpf2 : (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half}
          (W64 (sint.Z rev) : w64) : IProp GF) $$ [Hcmpf]
      · rw [← dfrac_own_half_half 1, hrw]; iexact Hcmpf
      icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).1 $$ Hcmpf2 with ⟨Hcmp, HcmpM⟩
      -- the caller's hook is the store's
      imod mvcc.hookP_agree_lc ⊤ γ P Ph f $$ [$Hlc2 $HhookC $Hhook] with ⟨#HPP0, #HP0P⟩
      ihave #HhookC' := HhookC
      iunfold mvcc.hookOk at HhookC'
      icases HhookC' with ⟨-, #Hhf⟩
      iunfold mvcc.csContract at Hcs
      icases Hcs with ⟨HPre, #Htriple, Hupd⟩
      ihave #Htr0 : □ ({{ Ph ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) $$ []
      · iintro !> %Φ' !> ⟨HP0, Hpre⟩ HΦ'
        iapply Htriple $$ %Φ' [HP0 Hpre] HΦ'
        iframe Hpre
        iapply HP0P
        iexact HP0
      -- `SetScheduledCompact(s.b.BatchTx(), rev)`, over the store's contract with its compaction on
      -- (question 5's core stage, parts (2)-(4): its tokens, lock resource and write right)
      have hcM := mvcc.storeCmp_cmpM γ hcmp
      ihave #Hbk' := mvcc.isKeyBackendG_cmpOn b s γ Dep Ph (mvcc.hookFn γ) hcmp $$ Hbk
      -- Q1 (a): the store's facts only through `physCmpD`, the supply from the pre
      ihave #HmwD := mvcc.physCmpD_of_physCmp s γ $$ HmwP
      iclear HmwP
      ihave #Hsw := mvcc.mwSwap_of_physCmpD s γ hcM $$ HmwD
      icases (mvcc.physCmpD_on s γ hcM).1 $$ HmwD with ⟨-, #Hreg⟩
      ihave #Hsup := (mvcc.kbWTSupplyM_on γ.kb hcM).1 $$ HsupM
      iunfold mvcc.isKeyBackendG at Hbk'
      icases Hbk' with ⟨%bi, %Hbi, -, -, #HB, #HForce, -⟩
      subst Hbi
      (try wp_auto)
      wp_bind (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      iapply HB $$ [] [-]
      · itrivial
      inext
      iintro %bt #Hbt
      -- a write-back token for the session, from the supply and a step's receipt
      wp_take_receipt as Hr1
      imod mvcc.kbWTSupply_take γ.kb $$ [$Hsup $Hr1] with Hwt1
      (try wp_auto)
      iunfold mvcc.isBatchTxG at Hbt
      icases Hbt with ⟨%Locked, %LockedO, #Hbt, -⟩
      have hrev0 : 0 ≤ sint.Z rev := by omega
      -- (`wp_apply` of a triple over `Locked`, a variable from an existential, leaves a synthetic
      -- `sorry`: bind and apply)
      wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.SetScheduledCompact))
        (Val #(GoInterface.ok bt))) (Val #rev))
      -- (question 5's core stage) the store's swap of its lock's resource for the right
      iapply (h3 bt (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ) (mvcc.storePutOk γ)
          (mvcc.delKey γ) (mvcc.storeW s γ) Dep Locked Ph (mvcc.hookFn γ) (mvcc.storeRb γ)
          (mvcc.kbMW γ.kb γ.bucket) f rev Pre Q Post hrev0) $$ [HPre Hupd HRTok Hwt1]
      · iframe #
        iframe HPre HRTok Hwt1
        iintro ⟨HQ, HW⟩
        imod Hupd $$ HQ with ⟨HP, HPost⟩
        ihave HP0 := HPP0 $$ HP
        ihave HW := mvcc.storeW_get s γ $$ [$Hreg $HW]
        iunfold mvcc.writerRes at HW
        icases HW with ⟨%ilog, HW⟩
        iNamed HW
        iunfold mvcc.compactRes at Hcres
        icases Hcres with ⟨%sch, %fin, %n, Hmeta, Hfin, %Hn, Hmk⟩
        iunfold mvcc.metaCompact at Hmeta
        imod ghostVar_update (some rev, fin) γ.cmeta _ $$ Hmeta with Hmeta
        imodintro
        iframe HP0 HPost
        iapply mvcc.storeW_put s γ
        iframe Hreg
        iunfold mvcc.writerRes
        iexists ilog
        simp only [named]
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hne
        iunfold mvcc.compactRes
        iexists (some rev), fin, n
        iunfold mvcc.metaCompact
        iframe
        ipureintro; exact Hn
      inext
      iintro ⟨HRTok, HPost⟩
      -- `s.b.ForceCommit()`, with a write-back token from the supply
      imod mvcc.kbWTSupply_take γ.kb $$ [$Hsup $Hr2] with Hwt2
      (try wp_auto)
      wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
      iapply HForce $$ %iprop(True) %iprop(True) [HRTok Hwt2] [-]
      · iframe HRTok Hwt2
        isplitr; · itrivial
        iapply mvcc.storeReq_true
      inext
      iintro ⟨HRTok, -⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev HrstR]
      · iframe #
        inext
        iapply mvcc.revMuInv_close; iframe HrstR; iunfold mvcc.revMuBody
        iexists log, ntok, sint.Z rev
        simp only [named]
        rw [hrw]
        iframe
        iframe #
        ipureintro; exact ⟨Hne, Hbudget, by omega, by omega⟩
      (try wp_auto)
      iapply HΦ
      iframe HRTok
      isplitl [HwFrag]
      · iapply (mvcc.hookIs_split γ P f).2; iframe HwFrag HhookC
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, Hgt⟩
      isplitl [HcmpM HcrevM]
      · iunfold mvcc.muInvAt; simp only [named]
        rw [hrw]
        iframe
        isplitr
        · iunfold mvcc.crevSafe; iexists logc; iframe HcertC; ipureintro; exact HndC
        ipureintro; omega
      isplitl [Hcr Hq]
      · iunfold mvcc.compactRight
        iframe Hcr Hlive
        iapply mvcc.compactQueue_mono γ c' (sint.Z rev) (by omega) $$ Hq
      iframe HPost
      -- the caller's `NoDelPutAt`, for the committed log (`crevSafe_cert`)
      ihave %Hnd' : ⌜mvcc.NoDelPutAt log (sint.Z rev)⌝ $$ []
      · iapply mvcc.crevSafe_cert γ (sint.Z rev) log hrl $$ [Hcert]
        iframe Hcert
        iunfold mvcc.crevSafe; iexists logc; iframe HcertC; ipureintro; exact HndC
      iunfold mvcc.compactJobPreD -- Q1 (a)
      iframe #
      isplitr
      · ipureintro; exact hcmp
      ipureintro
      exact ⟨by omega, hrl, Hnd'⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem mvcc.store.scheduleCompaction.wp_proofD
    (h0 : mvcc.treeIndex.Compact.spec (GF := GF) (hG := hG))
    (h2 : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG))
    (h3 : mvcc.newKVHasher.spec (GF := GF) (hG := hG))
    (h4 : mvcc.BytesToRev.spec (GF := GF) (hG := hG))
    (h5 : mvcc.kvHasher.WriteKeyValue.spec (GF := GF) (hG := hG))
    (h6 : mvcc.UnsafeSetFinishedCompact.spec (GF := GF) (hG := hG))
    (h7 : mvcc.kvHasher.Hash.spec (GF := GF) (hG := hG))
    (h8 : zap.Int64.spec (GF := GF) (hG := hG))
    (h9 : zap.Duration.spec (GF := GF) (hG := hG))
    (h10 : zap.Int'.spec (GF := GF) (hG := hG))
    (h11 : zap.Uint32.spec (GF := GF) (hG := hG))
    (h12 : zap.String.spec (GF := GF) (hG := hG))
    (h13 : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (h14 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h15 : mvcc.RevToBytes.spec (GF := GF) (hG := hG))
    (h16 : time.Time.Unix.spec (GF := GF) (hG := hG)) :
    mvcc.store.scheduleCompaction.specD (GF := GF) (hG := hG) := by
  intro s γ rev prev
  wp_start as ⟨#Hjob, Htok⟩
  iunfold mvcc.compactJobPreD at Hjob -- Q1 (a): the supply in the job's premise
  icases Hjob with ⟨#Hs, #Hstop, -, %Hcmp, #Hlb, #HsupM, %log, #Hcert, #Hnevc, %Hrev'⟩
  have Hrev : 0 ≤ sint.Z rev ∧ sint.Z rev < log.length := ⟨Hrev'.1, Hrev'.2.1⟩
  have Hnd : mvcc.NoDelPutAt log (sint.Z rev) := Hrev'.2.2
  ihave %Hsmall : ⌜mvcc.CompactSmall log (sint.Z rev)⌝ $$ []
  · iapply mvcc.CompactSmall_of_cert s γ log (sint.Z rev) $$ [Hs Hcert]
    iframe Hs Hcert
  ihave #Hs0 := Hs
  iunfold mvcc.isStore at Hs0
  iNamed Hs0
  -- the compaction's objects, the current ones for good (D22 receiver epochs, S5b: until then
  -- `isStore`'s, pinned)
  icases mvcc.storeStop_open s γ $$ Hstop with
    ⟨%b, %ti, %ssched, %sstop, #Hb, #Hidx, #Hsched, #Hstopc, #Hstopch, #Hrstd, #Hph, #Hcurd⟩
  iunfold mvcc.physOk at Hph
  iNamed Hph
  try simp only
  -- (question 5's core stage) the store's compaction facts: the write right's invariant (the swap
  -- of the key for the compaction keys' write right), its registration, the write-back supply
  have hcmpM : mvcc.kbCmpM γ.kb := mvcc.storeCmp_cmpM γ Hcmp
  -- Q1 (a): the store's facts only through `physCmpD`, the supply from the job's premise
  ihave #HmwD := mvcc.physCmpD_of_physCmp s γ $$ HmwP
  iclear HmwP
  icases (mvcc.physCmpD_on s γ hcmpM).1 $$ HmwD with ⟨#Hmwi, #Hreg⟩
  ihave #Hsup := (mvcc.kbWTSupplyM_on γ.kb hcmpM).1 $$ HsupM
  ihave #Hswk := mvcc.mwSwap_of_inv γ iprop(True) $$ Hmwi
  -- the store's contract with its compaction on (its tokens, lock resource, slots, write right)
  ihave #Hbk' := mvcc.isKeyBackendG_cmpOn _ s γ _ _ _ Hcmp $$ Hbk
  iunfold mvcc.isKeyBackendG at Hbk'
  icases Hbk' with ⟨%bi, %Hbi, -, -, #HBT, #HForce, #HSize, #HSizeU, #HCmp⟩
  icases HCmp $$ [] with ⟨#HLSR, #HUSR, -⟩
  · ipureintro; trivial
  subst Hbi
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%hIdx, #HIdxG, #HIdx⟩, ⟨%hPause, #HPauseG, #HPause⟩, ⟨%hTot, #HTotG, #HTot⟩,
    ⟨%cKeys, #HKeysG, #HKeys⟩, ⟨%gLast, #HLastG, #HLast⟩, -⟩
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold mvcc.compactTok at Htok
  icases Htok with ⟨⟨%c', %hc', Htok⟩, Hjr⟩
  -- the job's budgets (question 5's core stage): its reader's token, the safe-range slot
  icases (mvcc.compactJobResM_on γ.kb hcmpM).1 $$ Hjr with ⟨HRT, HSR⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply HLSR $$ [$HSR] as HSRh
  (try wp_auto)
  wp_apply time.wp_Now as %t0 -
  (try wp_auto)
  wp_apply h0 ti γ.idx rev log c' $$ [$Htok] as %keep ⟨Htok, %A, Hkeep, %HA⟩
  · iframe #; ipureintro; exact ⟨hc', Hrev.1, Hrev.2⟩
  (try wp_auto)
  iunfold histSpec at HIdx HPause HTot
  iunfold counterSpec at HKeys
  icases HKeys with ⟨-, -, #HKeysAdd⟩
  iunfold gaugeSetSpec at HLast
  wp_apply time.wp_Since as %d1 -
  (try wp_auto)
  wp_apply HIdx
  (try wp_auto)
  wp_apply time.wp_Now as %t1 -
  (try wp_auto)
  wp_apply wp_slice_make2 (V := w8) (W64 8) as %endS ⟨HendS, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply (wp_bePutUint64 h2 endS _ (rev + W64 1) (by simp)) $$ [$HendS] as HendS
  (try wp_auto)
  ihave #HcfgS := Hcfg
  iStructNamedSuffix HcfgS "C"
  (try wp_auto)
  wp_apply h3 as %hv %Hhv
  (try wp_auto)
  wp_apply wp_slice_make2 (V := w8) (W64 17) as %lastS ⟨HlastS, HlastC⟩
  · ipureintro; decide
  (try wp_auto)
  -- the schema's `Key` bucket
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩, -⟩
  ihave #Hc2 := Hcert
  iunfold mvcc.idxCert at Hc2
  icases Hc2 with ⟨-, %Hlwf, -⟩
  have Hrz : sint.Z rev < 2 ^ 63 - 1 := by have := Hrev.2; have := Hlwf.2.1; omega
  irename «end» => endP
  -- the batches
  -- `D`: the keys deleted so far (item 8): distinct keys of the job's space, below the cursor
  ihave HI : iprop(∃ (lst : GoSlice) (bs : List w8) (kc : w64) (hv' : kvHasher) (D : List GoString),
      "last" ∷ last_ptr ↦ lst ∗ "HlastS" ∷ lst ↦* bs ∗ "HlastC" ∷ ownSliceCap w8 lst (DFrac.own 1) ∗
      "%Hbs" ∷ ⌜bs.length = 17⌝ ∗ "keyCompactions" ∷ keyCompactions_ptr ↦ kc ∗
      "h" ∷ (h_ptr ↦ hv' ∗ ⌜mvcc.kvHasherOk hv'⌝) ∗
      "%HD" ∷ ⌜sint.Z kc = D.length ∧ D.Nodup ∧
        ∀ k ∈ D, mvcc.sc_space log (sint.Z rev) k ∧ go.GoStringLt k bs⌝)
    $$ [last HlastS HlastC keyCompactions h]
  · iexists lastS, _, W64 0, hv, []
    simp only [named]
    iframe
    ipureintro; simp [Hhv]
  wp_for HI
  wp_apply +noauto time.wp_Now as %tst -
  -- (question 5's core stage) a receipt for the session's write-back token
  wp_take_receipt as Hr1
  imod mvcc.kbWTSupply_take γ.kb $$ [$Hsup $Hr1] with Hwt1
  (try wp_auto)
  wp_apply HBT as %bt #Hbt
  (try wp_auto)
  iunfold mvcc.isBatchTxG at Hbt
  icases Hbt with ⟨%Locked, %LockedO, #HbtS, -⟩
  ihave #HbtS0 := HbtS
  iunfold mvcc.batchTxSpecG at HbtS0
  icases HbtS0 with ⟨-, -, -, -, -, #HLockOut, #HRng, -⟩
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HLockOut $$ [HRT Hwt1]
  · iframe HRT Hwt1; iframe #
  inext
  iintro ⟨Hlocked, HW, HP, HRT⟩
  ihave HW := mvcc.storeW_get s γ $$ [$Hreg $HW]
  -- (question 5's core stage, part (1)) a later credit for the last batch's swap of the key
  wp_auto_lc 1
  iunfold mvcc.writerRes at HW
  icases HW with ⟨%ilog, HW⟩
  iNamedSuffix HW "W"
  ihave #HcW' := HcertW
  ihave %Hpre : ⌜log <+: ilog ∨ ilog <+: log⌝ $$ []
  · iapply mvcc.idxCert_prefix $$ [Hcert HcertW]
    iframe Hcert HcertW
  iunfold mvcc.idxCert at HcW'
  icases HcW' with ⟨-, %HilWf, -⟩
  ispecialize HRng $$ []
  · ipureintro; trivial
  wp_bind (App (App (App (App (Val #(methods bt.ty _ bt.v)) (Val #bK)) (Val #lst)) (Val #endS)) (Val #_))
  iapply HRng $$ %(1 : Qp).half %(mvcc.bucketMap ilog) %bK %lst %endS %bs %(u64Be (rev + W64 1))
    %scfg.CompactionBatchLimit' %(DFrac.own 1) %(DFrac.own 1) [] [Hlocked HbvW HlastS HendS]
  · ipureintro
    refine ⟨Hcfgl.1, Hcfgl.2, ?_⟩
    intro hn
    have := congrArg List.length hn
    simp [u64Be_length] at this
  · iframe; iframe #
  inext
  -- (the backend-compaction stage, R2-3) the session ends in the range's token `U`, at the budget
  -- `limit + 1`: a delete or the `Meta` put spends one, `Unlock` takes any
  iintro %ks %vs ⟨HbvW, HlastS, HendS, %m', %Rd, %U, HU, #Hthin, #Hcap, #Hcap2, #Hpv,
    #HDelC, #HMetaC, #HUnlU⟩
  (try wp_auto)
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  iunfold mvcc.snapThin at Hthin
  icases Hthin with ⟨%Hsub, -⟩
  (try simp only [List.foldl_nil] at Hsub)
  generalize hL : (mvcc.bucketRange m' bs (u64Be (rev + W64 1))).take
    (sint.Z scfg.CompactionBatchLimit').toNat = L
  have HLent : ∀ p ∈ L, ∃ (r : mvcc.Rev) (t : Bool), p.1 = mvcc.revBytes r t ∧ 0 ≤ sint.Z r.main ∧
      0 ≤ sint.Z r.sub ∧ sint.Z r.main ≤ sint.Z rev := by
    intro p hp
    rw [← hL] at hp
    exact mvcc.sc_entry HilWf.2.2 HilWf.2.1 Hsub bs rev Hrev.1 Hrz _ hp
  have HLsrt : (L.map Prod.fst).Pairwise go.GoStringLt := by
    rw [← hL]
    exact (((mvcc.bucketRange_eq_iff _ _ _ _).1 rfl).1).sublist
      (List.Sublist.map _ (List.take_sublist _ _))
  have HLmem : ∀ p ∈ L, m'.lookup p.1 = some p.2 ∧ go.GoStringLe bs p.1 := by
    intro p hp
    rw [← hL] at hp
    have := (((mvcc.bucketRange_eq_iff m' bs _ _).1 rfl).2 p.1 p.2).1
      (by simpa using List.mem_of_mem_take hp)
    exact ⟨this.1, this.2.1⟩
  have Hlt_le : ∀ {a b c : GoString}, go.GoStringLt a b → go.GoStringLe b c → go.GoStringLt a c := by
    intro a b c h1 h2
    rcases h2 with rfl | h2
    · exact h1
    · exact go.goStringLt_trans h1 h2
  iunfold mvcc.pairVals at Hpv
  icases Hpv with ⟨%kss, %vss, #Hks, #Hvs, %Hlens, #Hel⟩
  ihave %Hvl := ownSlice_len _ _ _ $$ Hvs
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave IH : iprop(∃ (n k kc : w64) (hv : kvHasher) (rv : Revision) (D : List GoString),
      "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ k ∗ "keyCompactions" ∷ keyCompactions_ptr ↦ kc ∗
      "h" ∷ (h_ptr ↦ hv ∗ ⌜mvcc.kvHasherOk hv⌝) ∗ "rev" ∷ rev_ptr ↦ rv ∗
      "Hlocked" ∷ (∃ c : Nat, U c ∗ ⌜L.length + 1 ≤ c + sint.nat n⌝) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ L.length⌝ ∗
      "%HD" ∷ ⌜sint.Z kc = D.length ∧ D.Nodup ∧ (∀ k ∈ D, mvcc.sc_space log (sint.Z rev) k) ∧
        (∀ k ∈ D, ∀ j (hj : j < L.length), sint.nat n ≤ j → go.GoStringLt k (L[j]).1) ∧
        (sint.Z n = 0 ∨ ∀ k ∈ D, go.GoStringLt k
          (mvcc.revBytes (mvcc.revOf ⟨rv.Main', rv.Sub' + W64 1⟩) false))⌝)
    $$ [i Higo keyCompactions h rev HU]
  · iexists W64 0, _, _, _, _, D
    simp only [named]
    ihave HU : iprop(∃ c : Nat, U c ∗ ⌜L.length + 1 ≤ c + sint.nat (W64 0)⌝) $$ [HU]
    · iexists _; iframe HU; ipureintro
      have : L.length ≤ (sint.Z scfg.CompactionBatchLimit').toNat := by
        rw [← hL]; exact List.length_take_le _ _
      have h0 : sint.nat (W64 0) = 0 := by decide
      rw [h0]; omega
    iframe
    ipureintro
    refine ⟨⟨by decide, by simp⟩, HD.1, HD.2.1, fun k hk => (HD.2.2 k hk).1, ?_, Or.inl (by decide)⟩
    intro k hk j hj _
    exact Hlt_le (HD.2.2 k hk).2 (HLmem _ (List.getElem_mem hj)).2
  wp_for IH
  wp_if_destruct
  · have hlen1 : kss.length = L.length := by simpa using Hlens.1
    have hlen2 : vss.length = L.length := by simpa using Hlens.2
    have Hlt : sint.nat n < L.length := by rw [← hlen1, Hkl.1]; word
    have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ks.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd2, and_self, ↓reduceIte]
    obtain ⟨e, He⟩ : ∃ e, L[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases (BigSepL.bigSepL_lookup_acc He).1 $$ Hel with ⟨⟨%ksl, %vsl, %Hkv, #Hksl, #Hvsl⟩, -⟩
    obtain ⟨r, t, Hk, Hr0, Hs0, Hrm⟩ := HLent e (List.mem_of_getElem? He)
    wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
    · ipureintro; exact Hkv.1
    (try wp_auto)
    simp only [Hbnd2, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
    · ipureintro; exact Hkv.1
    have Hkb : e.1 = mvcc.revBytes r false ++ (if t then [W8 116] else []) := by
      rw [Hk]; cases t <;> simp [mvcc.revBytes]
    -- (backend-cmp, 3.5; R2-3) the key slice read under the range's token
    icases Hlocked with ⟨%c, Hlocked, %Hc⟩
    ihave #Hcap' := Hcap $$ %c
    iunfold mvcc.rdCap at Hcap'
    icases Hcap' $$ %ksl %e.1 Hksl Hlocked with ⟨%dqk, Hkp, Hkback⟩
    wp_apply (h4 ksl r (if t then [W8 116] else []) dqk (by cases t <;> simp) Hr0 Hs0)
      $$ [Hkp] as Hkp
    · rw [← Hkb]; iexact Hkp
    ihave Hlocked := Hkback $$ [Hkp]
    · rw [Hkb]; iexact Hkp
    (try wp_auto)
    wp_apply (wp_map_lookup2 Revision.ty (go.GoType.StructType []) keep A (mvcc.revVal r) (DFrac.own 1))
      $$ [$Hkeep] as Hkeep
    (try wp_auto)
    obtain ⟨HnL, HeL⟩ := List.getElem?_eq_some_iff.1 He
    have Henotin : e.1 ∉ D := fun hm =>
      go.goStringLt_irrefl _ (by have := HD.2.2.2.1 e.1 hm (sint.nat n) HnL (Nat.le_refl _); rwa [HeL] at this)
    have Hesp : mvcc.sc_space log (sint.Z rev) e.1 :=
      mvcc.sc_mem log ilog rev Hrev.2 HilWf.2.1 Hpre Hsub (HLmem e (List.mem_of_getElem? He)).1 r t
        Hk Hrm
    wp_join iprop(∃ (kc' : w64) (D' : List GoString), keyCompactions_ptr ↦ kc' ∗
        (∃ c' : Nat, U c' ∗ ⌜L.length + 1 ≤ c' + (sint.nat n + 1)⌝) ∗
        keys_ptr ↦ ks ∗ igo ↦ n ∗ tx_ptr ↦ GoInterface.ok bt ∗
        ⌜sint.Z kc' = D'.length ∧ D'.Nodup ∧ (∀ k ∈ D', mvcc.sc_space log (sint.Z rev) k) ∧
          ∀ k ∈ D', k = e.1 ∨ k ∈ D⌝)
      with [keyCompactions Hlocked keys Higo tx]
      as ⟨%kc', %D', keyCompactions, Hlocked, keys, Higo, tx, %HD'⟩
    · iexists kc, D
      ihave Hlocked : iprop(∃ cc : Nat, U cc ∗ ⌜L.length + 1 ≤ cc + (sint.nat n + 1)⌝) $$ [Hlocked]
      · iexists c; iframe Hlocked; ipureintro; omega
      iframe
      ipureintro
      exact ⟨HD.1, HD.2.1, HD.2.2.1, fun k hk => Or.inr hk⟩
    · (try wp_auto)
      simp only [Hbnd2, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
      · ipureintro; exact Hkv.1
      ihave #Hdk : mvcc.delKey γ e.1 $$ []
      · iunfold mvcc.delKey
        iexists (sint.Z rev), log
        iframe Hlb Hcert
        ipureintro
        refine ⟨by omega, mvcc.sc_keyDel log rev A HA Hrev.2 r t e.1 Hk Hr0 Hrm ?_, Hnd⟩
        revert Hif; cases (A !! mvcc.revVal r).isSome <;> simp
      (try wp_auto)
      wp_bind (App (App (Val #(methods bt.ty _ bt.v)) (Val #bK)) (Val #ksl))
      -- (Draft round 2) the key slice `keys[i]` passed lent, as the range returned it; (R2-3) one
      -- of the range's budget spent (`c ≥ 2`: a key left to read, and the `Meta` put's)
      obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 1 := ⟨c - 1, by omega⟩
      iapply HDelC $$ %ksl %e.1 %c'' [Hlocked]
      · iframe Hlocked; iframe #
      inext
      iintro Hlocked
      (try wp_auto)
      wp_join_done
      -- the key deleted: one more in `D`, still fewer than the job's changes
      have Hnd' : (e.1 :: D).Nodup := List.nodup_cons.2 ⟨Henotin, HD.2.1⟩
      have Hsp' : ∀ k ∈ e.1 :: D, mvcc.sc_space log (sint.Z rev) k := by
        intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · exact Hesp
        · exact HD.2.2.1 k hk
      have Hcnt := mvcc.sc_count log (sint.Z rev) _ Hnd' Hsp'
      have Hsm : ((log.take ((sint.Z rev).toNat + 1)).map List.length).sum < 2 ^ 62 := Hsmall
      rw [List.length_cons] at Hcnt
      have HDk := HD.1
      iexists kc + W64 1, e.1 :: D
      ihave Hlocked : iprop(∃ cc : Nat, U cc ∗ ⌜L.length + 1 ≤ cc + (sint.nat n + 1)⌝) $$ [Hlocked]
      · iexists c''; iframe Hlocked; ipureintro; omega
      iframe
      ipureintro
      refine ⟨?_, Hnd', Hsp', fun k hk => ?_⟩
      · rw [List.length_cons]; word
      · rcases List.mem_cons.1 hk with rfl | hk
        · exact Or.inl rfl
        · exact Or.inr hk
    (try wp_auto)
    simp only [Hbnd2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
    · ipureintro; exact Hkv.1
    (try wp_auto)
    have Hbnd3 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z vs.len := by
      refine ⟨Hn.1, ?_⟩; have := Hvl.1; rw [hlen2] at this; word
    simp only [Hbnd3, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index vs (sint.Z n) vss DFrac.discard vsl Hn.1 $$ [$Hvs] as -
    · ipureintro; exact Hkv.2
    (try wp_auto)
    icases h with ⟨h, %Hhv⟩
    -- (backend-cmp, 3.5; R2-3) the key and its value read together under the range's token
    icases Hlocked with ⟨%c', Hlocked, %Hc'⟩
    ihave #Hcap2' := Hcap2 $$ %c'
    iunfold mvcc.rdCap2 at Hcap2'
    icases Hcap2' $$ %ksl %vsl %e.1 %e.2 Hksl Hvsl Hlocked with ⟨%dqk, %dqv, Hkp, Hvp, Hkvback⟩
    wp_apply (h5 h_ptr hv keep (DFrac.own 1) A ksl vsl e.1 e.2 dqk dqv)
      $$ [$h $Hkeep $Hkp $Hvp] as ⟨⟨%hv2, h⟩, Hkeep, Hkp, Hvp⟩
    · iframe #
      ipureintro
      exact ⟨Hhv, r, _, Hkb, by cases t <;> simp, Hr0, Hs0⟩
    ihave Hlocked := Hkvback $$ Hkp Hvp
    (try wp_auto)
    wp_for_post
    iframe
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    ihave Hlocked : iprop(∃ cc : Nat, U cc ∗ ⌜L.length + 1 ≤ cc + sint.nat (n + W64 1)⌝) $$ [Hlocked]
    · iexists c'; iframe Hlocked; ipureintro; rw [Hn1]; exact Hc'
    iexists n + W64 1, n, kc', hv2, mvcc.revVal r, D'
    simp only [named]
    iframe
    ipureintro
    have Hsrt := List.pairwise_iff_getElem.1 HLsrt
    have Hnext : ∀ j (hj : j < L.length), sint.nat n < j → go.GoStringLt e.1 (L[j]).1 := by
      intro j hj hnj
      have := Hsrt (sint.nat n) j (by simpa using HnL) (by simpa using hj) hnj
      simpa [HeL] using this
    have Hsucc : go.GoStringLt e.1
        (mvcc.revBytes (mvcc.revOf ⟨(mvcc.revVal r).Main', (mvcc.revVal r).Sub' + W64 1⟩) false) := by
      rw [Hk]
      apply mvcc.RevOrder.revBytes_lt
      right
      simp only [mvcc.revOf, mvcc.revVal]
      refine ⟨?_, ?_⟩ <;> first | trivial | rfl | word
    refine ⟨⟨by word, by word⟩, HD'.1, HD'.2.1, HD'.2.2.1, ?_, Or.inr ?_⟩
    · intro k hk j hj hnj
      rcases HD'.2.2.2 k hk with rfl | hk
      · exact Hnext j hj (by omega)
      · exact HD.2.2.2.1 k hk j hj (by omega)
    · intro k hk
      rcases HD'.2.2.2 k hk with rfl | hk
      · exact Hsucc
      · exact go.goStringLt_trans
          (by have := HD.2.2.2.1 k hk (sint.nat n) HnL (Nat.le_refl _); rwa [HeL] at this) Hsucc
  -- (R2-3) the range's token at the loop's end: one left at least, for the `Meta` put
  icases Hlocked with ⟨%c, HU, %Hc⟩
  have HnL' : sint.nat n ≤ L.length := Hn.2
  obtain ⟨c0, rfl⟩ : ∃ c0, c = c0 + 1 := ⟨c - 1, by omega⟩
  -- the batch read: short (the last), or full
  wp_if_destruct
  · -- the last batch: `finishedCompactRev = rev`, the compaction finished
    (try wp_auto)
    -- (question 5's core stage, part (1)) the key in the batch lock's resource, swapped for the
    -- compaction keys' write right for the `Meta` put, and back
    iunfold mvcc.compactRes at HcresW
    icases HcresW with ⟨%sched, %fin, %nf, Hmeta, Hfin, %Hnf, Hmk⟩
    ihave Hmk := (mvcc.mwSlot_on γ hcmpM).1 $$ Hmk
    iunfold mvcc.mwSwap at Hswk
    imod Hswk $$ [Hmk Hlc1] with ⟨HMW, Hback⟩
    · iframe Hmk Hlc1
    wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact))
      (Val #(GoInterface.ok bt))) (Val #rev))
    iapply (h6 bt iprop(U (c0 + 1) ∗ mvcc.kbMW γ.kb γ.bucket) iprop(U c0 ∗ mvcc.kbMW γ.kb γ.bucket)
      rev Hrev.1) $$ [HU HMW]
    · iframe HU HMW; iframe #
      iapply HMetaC
    inext
    iintro ⟨HU, HMW⟩
    imod Hback $$ HMW with ⟨Hmk, -⟩
    ihave Hmk := (mvcc.mwSlot_on γ hcmpM).2 $$ Hmk
    (try wp_auto)
    iunfold mvcc.metaCompact at Hmeta
    imod ghostVar_update (sched, some rev) γ.cmeta _ $$ Hmeta with Hmeta
    imod mono_nat_own_update (max nf (mvcc.crevN (sint.Z rev))) (Nat.le_max_left _ _) $$ Hfin
      with ⟨Hfin, #Hflb⟩
    ihave #Hdone : mvcc.compactedAt γ (sint.Z rev) $$ []
    · iunfold mvcc.compactedAt
      iapply monoNatLbOwn_le _ (Nat.le_max_right _ _) $$ Hflb
    wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
    iapply HUnlU $$ %c0 [HU HwkW HwvW HbvW Hmeta Hfin Hmk HP]
    · iframe HU HP
      iapply mvcc.storeW_put s γ
      iframe Hreg
      iunfold mvcc.writerRes
      iexists ilog
      simp only [named]
      iframe
      iframe #
      isplitr
      · ipureintro; exact HneW
      iunfold mvcc.compactRes
      iexists sched, some rev, _
      iunfold mvcc.metaCompact
      iframe
      ipureintro
      exact Nat.le_max_right _ _
    inext
    iintro -
    (try wp_auto)
    wp_apply time.wp_Since as %d2 -
    (try wp_auto)
    wp_apply HPause
    (try wp_auto)
    icases h with ⟨h, %Hhv⟩
    wp_apply h7 h_ptr hv $$ [$h] as %hash h
    · ipureintro; exact Hhv
    (try wp_auto)
    wp_apply HSize as %sz -
    wp_apply HSizeU as %szu -
    (try wp_auto)
    wp_apply h8 as %f0 -
    (try wp_auto)
    wp_apply time.wp_Since as %d3 -
    (try wp_auto)
    wp_apply h9 as %f1 -
    (try wp_auto)
    wp_apply h10 as %f2 -
    (try wp_auto)
    wp_apply h11 as %f3 -
    (try wp_auto)
    wp_apply h8 as %f4 -
    (try wp_auto)
    wp_apply h13 as %str5 -
    (try wp_auto)
    wp_apply h12 as %f5 -
    (try wp_auto)
    wp_apply h8 as %f6 -
    (try wp_auto)
    wp_apply h13 as %str7 -
    (try wp_auto)
    wp_apply h12 as %f7 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1, f2, f3, f4, f5, f6, f7]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h14 lg _ _ $$ []
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_for_post
    wp_apply time.wp_Now as %tn -
    (try wp_auto)
    wp_apply h16 as %un -
    (try wp_auto)
    wp_apply HLast
    (try wp_auto)
    have hkc0 : 0 ≤ sint.Z kc := by have := HD.1; omega
    ihave #HKA := HKeysAdd $$ %kc %hkc0
    wp_apply HKA
    (try wp_auto)
    wp_apply time.wp_Since as %d4 -
    (try wp_auto)
    wp_apply HTot
    (try wp_auto)
    wp_apply HUSR $$ [$HSRh] as HSR
    (try wp_auto)
    iapply HΦ
    iframe Htok
    isplitl [HRT HSR]
    · iapply (mvcc.compactJobResM_on γ.kb hcmpM).2; iframe HRT HSR
    ileft
    iframe Hdone
    ipureintro; rfl
  -- a full batch: committed, then the next one after the sleep, unless the store stops
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HUnlU $$ %(c0 + 1) [HU HwkW HwvW HbvW HcresW HP]
  · iframe HU HP
    iapply mvcc.storeW_put s γ
    iframe Hreg
    iunfold mvcc.writerRes
    iexists ilog
    simp only [named]
    iframe
    iframe #
    ipureintro; exact HneW
  inext
  iintro -
  -- (question 5's core stage) a receipt for `ForceCommit`'s write-back token
  wp_take_receipt as Hr2
  imod mvcc.kbWTSupply_take γ.kb $$ [$Hsup $Hr2] with Hwt2
  wp_apply (h15 _ lst bs (Or.inl Hbs)) $$ [$HlastS $HlastC] as %lst2 ⟨HlastS, HlastC⟩
  (try wp_auto)
  wp_apply HForce $$ %iprop(True) %iprop(True) [HRT Hwt2] as ⟨HRT, -⟩
  · iframe HRT Hwt2
    isplitr; · itrivial
    iapply mvcc.storeReq_true
  (try wp_auto)
  wp_apply time.wp_Since as %d5 -
  (try wp_auto)
  wp_apply HPause
  (try wp_auto)
  wp_apply +noauto time.wp_After as %tch %γt #Hbag
  wp_auto_lc 2
  ihave #Hstc := Hstopc
  ihave #Hstcc := Hstopch
  iunfold mvcc.isStopChan at Hstcc
  icases Hstcc with ⟨%γs, #Hstcc⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %tm' -
    wp_auto
    wp_for_post
    iframe
    have HDk := HD
    iexists lst2, _, kc, hv, D
    simp only [named]
    iframe
    ipureintro
    refine ⟨by rw [List.length_append, mvcc.revBytes_length]; simp [Hbs], HD.1, HD.2.1,
      fun k hk => ⟨HD.2.2.1 k hk, ?_⟩⟩
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
    rcases HD.2.2.2.2 with h0 | hlt
    · exfalso
      clear HDk
      exact absurd h0 (by omega)
    · exact hlt k hk
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sstop, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hstcc
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hstcc
    iintro ⟨-, #Hdone⟩
    wp_auto
    wp_apply mvcc.wp_Errorf_errorfIs $$ [] as %err #Herr
    · iframe #; iapply ownSlice_nil
    (try wp_auto)
    wp_for_post
    wp_apply time.wp_Now as %tn -
    (try wp_auto)
    wp_apply h16 as %un -
    (try wp_auto)
    wp_apply HLast
    (try wp_auto)
    have hkc0 : 0 ≤ sint.Z kc := by have := HD.1; omega
    ihave #HKA := HKeysAdd $$ %kc %hkc0
    wp_apply HKA
    (try wp_auto)
    wp_apply time.wp_Since as %d4 -
    (try wp_auto)
    wp_apply HTot
    (try wp_auto)
    wp_apply HUSR $$ [$HSRh] as HSR
    (try wp_auto)
    iapply HΦ
    iframe Htok
    isplitl [HRT HSR]
    · iapply (mvcc.compactJobResM_on γ.kb hcmpM).2; iframe HRT HSR
    iright
    iframe Herr
    iunfold mvcc.storeStopped
    iexists sstop, γs
    iframe Hstc Hdone
  iapply BigAndL.bigAndL_nil.2
  itrivial
theorem mvcc.store.compact.wp_proofD
    (h0 : schedule.NewJob.spec (GF := GF) (hG := hG))
    (h1 : context.Err.spec (GF := GF) (hG := hG))
    (h2 : mvcc.store.compactBarrier.spec (GF := GF) (hG := hG))
    (h3 : mvcc.store.scheduleCompaction.specD (GF := GF) (hG := hG))
    (h4 : zap.Error.spec (GF := GF) (hG := hG))
    (h5 : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h6 : mvcc.hashStorage.Store.spec (GF := GF) (hG := hG))
    (h7 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h8 : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG))
    (h9 : traceutil.Trace.Step.spec (GF := GF) (hG := hG)) :
    mvcc.store.compact.specD (GF := GF) (hG := hG) := by
  intro s γ trace rev prev pcc te Htr
  wp_start as ⟨#Hjob, Hq, Htrc⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %ch %γc ⟨#Hc, %Hcap, Hown⟩
  imod alloc_broadcast_chan (E := ⊤) (mvcc.compactDone s γ (sint.Z rev)) γc ch $$ Hc Hown with Hcl
  ihave #Hrcv := ownBroadcastChan_Unknown _ _ _ _ $$ Hcl
  (try wp_auto)
  -- the queue: the last tracked job's `Post` `Q`, with `R` the token's
  iunfold mvcc.compactQueue at Hq
  icases Hq with ⟨%Ps, %p, %Q, %R, Hq, #Hp, HR, Hw⟩
  imod (schedule.savedProp_alloc (mvcc.compactTok γ (sint.Z rev))) with ⟨%post, #Hpost⟩
  ipersist s
  ipersist rev
  ipersist prevCompactRev
  ipersist prevCompactionCompleted
  ipersist ch
  ihave #Hjob' := Hjob
  iunfold mvcc.compactJobPreD at Hjob' -- Q1 (a)
  icases Hjob' with ⟨#Hs, #Hstop, #Hlive, %Hcmp, #Hlb, -, #Hcert⟩
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  -- the compaction's objects, the current ones for good (D22 receiver epochs, S5b: until then
  -- `isStore`'s, pinned)
  icases mvcc.storeStop_open s γ $$ Hstop with
    ⟨%b, %ti, %ssched, %sstop, #Hb, #Hidx, #Hsched, #Hstopc, #Hstopch, #Hrstd, #Hph, #Hcurd⟩
  iunfold mvcc.physOk at Hph
  iNamed Hph
  try simp only
  wp_func_lits
  (try wp_auto)
  wp_apply (h0 γ.sch _ _
      iprop(mvcc.compactCloser ch (mvcc.compactDone s γ (sint.Z rev)) ∗ R ∗
        (Q ∗ R -∗ mvcc.compactTok γ (sint.Z rev)))
      Q (mvcc.compactTok γ (sint.Z rev))) $$ [] as %j #Hj
  · iframe #
    iunfold schedule.jobFnSpec
    iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨Hcl, HR, Hw⟩, HQ, #Hctx⟩ HΦj
    wp_auto
    ihave #HErrU := h1 ctx cd Broadcast.Unknown $$ Hctx
    wp_apply HErrU as %err Hm #HcS
    cases err with
    | ok e =>
      simp only [reduceCtorEq, ↓reduceIte]
      icases Hm with ⟨-, #Hclosed⟩
      wp_auto
      wp_apply (h2 s γ ctx cd ch (mvcc.compactDone s γ (sint.Z rev))) $$ [$Hcl]
      · iframe #
        isplitl []
        · iunfold mvcc.barrierCtx; iright; iexact Hctx
        iunfold mvcc.compactDone; iright; iright; iexists cd; iexact Hclosed
      (try wp_auto)
      iapply HΦj
      iframe Hrun
      iapply Hw; iframe HQ HR
    | nil =>
    simp only [↓reduceIte]
    wp_auto
    ihave Htok := Hw $$ [HQ HR]
    · iframe HQ HR
    wp_apply (h3 s γ rev prev) $$ [$Htok] as %h %err ⟨Hidx, Hjr, Hres⟩
    · iframe #
    ihave Htok : mvcc.compactTok γ (sint.Z rev) $$ [Hidx Hjr]
    · iunfold mvcc.compactTok; iframe Hjr; iexists (sint.Z rev); iframe Hidx; ipureintro; exact Int.le_refl _
    icases Hres with (⟨%Herr, #Hdone⟩ | ⟨Herr, #Hstopped⟩)
    · subst Herr
      wp_auto
      ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
      · iPkgInit
      wp_join with [hash]
      · (try wp_auto)
        wp_apply (h7 lg) $$ []
        · iframe #; ipureintro; exact Hlgnn
        wp_join_done
      · (try wp_auto)
        wp_apply (h6 shs h) $$ [$HhsOk]
        wp_join_done
      iunfold mvcc.compactCloser at Hcl
      icases Hcl with ⟨%γc', Hcl⟩
      wp_apply wp_broadcast_chan_close $$ [$Hcl] as -
      · iunfold mvcc.compactDone; ileft; iexact Hdone
      (try wp_auto)
      iapply HΦj
      iframe Hrun Htok
    · iunfold mvcc.errorfIs at Herr
      icases Herr with ⟨%x, %Hx, -⟩
      subst Hx
      wp_auto
      ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
      · iPkgInit
      wp_apply h4 as %fld -
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %flds -
      (try wp_auto)
      wp_apply (h5 lg) $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      wp_apply mvcc.wp_context_TODO_body
      (try wp_auto)
      wp_apply (h2 s γ mvcc.todoCtxV cd ch (mvcc.compactDone s γ (sint.Z rev))) $$ [$Hcl]
      · iframe #
        isplitl []
        · iunfold mvcc.barrierCtx; ileft; ipureintro; rfl
        iunfold mvcc.compactDone; iright; ileft; iexact Hstopped
      (try wp_auto)
      iapply HΦj
      iframe Hrun Htok
  (try wp_auto)
  -- `s.fifoSched.Schedule(j)`, tracked: `Q` the job's `Prev`, its `Post` saved as `post`
  ihave #Hfifo := HisSched
  ihave #Hfifo' := Hfifo
  iunfold schedule.isFifo at Hfifo'
  icases Hfifo' with ⟨%Hnn, -⟩
  cases ssched with
  | nil => exact absurd rfl Hnn
  | ok fi =>
  (try wp_auto)
  wp_apply (h8 fi γ.sch j
      iprop(mvcc.compactCloser ch (mvcc.compactDone s γ (sint.Z rev)) ∗ R ∗
        (Q ∗ R -∗ mvcc.compactTok γ (sint.Z rev)))
      Q (mvcc.compactTok γ (sint.Z rev)) (some (Ps, p, post))) $$ [Hcl HR Hw Hq] as Hq
  · iframe #
    simp only [schedule.schedPre]
    iframe Hq HR Hw Hp Hpost
    iunfold mvcc.compactCloser
    iexists γc; iexact Hcl
  simp only [schedule.schedPost]
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (h9 trace te _ slice.nil) $$ [Htrc] as Htrc
  · iframe #; iframe Htrc; iapply traceutil.ownFields_nil
  (try wp_auto)
  iapply HΦ
  iframe Htrc
  isplitr
  · iunfold mvcc.compactChan; iexists γc; iexact Hrcv
  iunfold mvcc.compactQueue
  iexists Ps ++ [p], post, mvcc.compactTok γ (sint.Z rev), iprop(True)
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  iframe Hq Hpost
  isplitr
  · itrivial
  iintro ⟨H, -⟩
  iexact H
theorem mvcc.store.compactLockfree.wp_proofD
    (h0 : mvcc.store.checkPrevCompactionCompleted.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.updateCompactRev.specD (GF := GF) (hG := hG))
    (h2 : traceutil.TODO.spec (GF := GF) (hG := hG))
    (h3 : mvcc.store.compact.specD (GF := GF) (hG := hG)) :
    mvcc.store.compactLockfree.specD (GF := GF) (hG := hG) := by
  intro s γ rev c P f Pre Q Post log hcmp
  wp_start as ⟨#Hs, #Hstop, Hmu, Hright, #HcertC, %HndC, Hhook, Hcs, HRTok, #HsupM⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (h0 s γ hcmp) $$ [$HRTok] as %pcc HRTok
  · iframe #
  (try wp_auto)
  wp_apply (h1 s γ rev c P f Pre Q Post log hcmp) $$ [$Hmu $Hright $Hcs $Hhook $HRTok] as %ch %prev %err ⟨HRTok, Hhook, Hres⟩
  · iframe #; ipureintro; exact HndC
  (try wp_auto)
  icases Hres with (⟨⟨%Herr, %Hch, %Hprev, %Hlt⟩, Hmu, Hright, HPost, #Hjob⟩ |
    ⟨⟨%Hle, %Hprev⟩, ⟨%ec, #Hec, %Herr⟩, Hmu, Hright, HPre, #Hch⟩ |
    ⟨⟨%Hlt, %Hch, %Hprev⟩, ⟨%ef, #Hef, %Herr⟩, #Hcert, Hmu, Hright, HPre⟩)
  · subst Herr
    (try wp_auto)
    wp_apply h2 as %t ⟨%Ht, Htrc⟩
    (try wp_auto)
    iunfold mvcc.compactRight at Hright
    icases Hright with ⟨Hcrev, Hq, #Hlive⟩
    wp_apply (h3 s γ t rev prev pcc true Ht) $$ [$Hjob $Hq $Htrc] as %ch' ⟨#Hch', Hq, -⟩
    (try wp_auto)
    iapply HΦ
    iframe HRTok Hhook
    ileft
    iframe Hmu HPost Hch'
    isplitr
    · ipureintro; exact ⟨rfl, Hlt⟩
    isplitl [Hcrev Hq]
    · iunfold mvcc.compactRight; iframe Hcrev Hq Hlive
    iunfold mvcc.compactJobPreD at Hjob -- Q1 (a)
    icases Hjob with ⟨-, -, -, -, #Hlb, -, -⟩
    iexact Hlb
  · subst Herr
    (try wp_auto)
    iapply HΦ
    iframe HRTok Hhook
    iright; ileft
    iframe Hmu Hright HPre Hch
    isplitr
    · ipureintro; exact Hle
    iexists ec; iframe Hec; ipureintro; rfl
  · subst Herr Hch
    (try wp_auto)
    iapply HΦ
    iframe HRTok Hhook
    iright; iright
    iframe Hmu Hright HPre
    isplitr
    · ipureintro; exact ⟨Hlt, rfl⟩
    iexists ef; iframe Hef; ipureintro; rfl
/-- `store.Compact` for a compaction right at a revision `c ≥ -1` (the store's compaction
revisions are: `-1` at `NewStore`, then each `Compact`'s `rev > c`). -/
theorem mvcc.store.Compact.wp_of_leD
    (h0 : mvcc.store.checkPrevCompactionCompleted.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.updateCompactRev.specD (GF := GF) (hG := hG))
    (h2 : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (h3 : mvcc.store.compact.specD (GF := GF) (hG := hG))
    (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : mvcc.Log) (te : Bool) (htr : trace ≠ null)
    (hcmp : mvcc.storeCmp γ) (hc : -1 ≤ c) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeStop s γ ∗ mvcc.compactRight γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.hookIs γ P f ∗
      mvcc.csContract P f Pre Q Post ∗ traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗
      mvcc.kbWTSupplyM γ.kb }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Compact")) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗ mvcc.hookIs γ P f ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.compactRight γ (sint.Z rev) ∗
        mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗ mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.compactRight γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        (∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜(log.length : Int) ≤ sint.Z rev⌝) ∗
        mvcc.compactRight γ c ∗ Pre)) }} := by
  wp_start as ⟨#Hs, #Hstop, Hright, #HcertC, %HndC, HhookW, Hcs, Htrc, HRTok, #HsupM⟩
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  -- the compaction's objects, the current ones for good (D22 receiver epochs, S5b: until then
  -- `isStore`'s, pinned)
  icases mvcc.storeStop_open s γ $$ Hstop with
    ⟨%b, %ti, %ssched, %sstop, #Hb, #Hidx, #Hsched, #Hstopc, #Hstopch, #Hrstd, #Hph, #Hcurd⟩
  iunfold mvcc.physOk at Hph
  iNamed Hph
  try simp only
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HmuP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ 1)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%c', HmuP, Hwr⟩
  iunfold mvcc.muInvAt at HmuP
  iNamed HmuP
  iunfold mvcc.compactRight at Hright
  icases Hright with ⟨Hcr, Hq, #Hlive⟩
  ihave %Hcc := mvcc.crevUB_agree γ.idx _ _ c' c HcM hc $$ HcrevM Hcr
  subst Hcc
  ihave Hmu1 : mvcc.muInvAt s γ 1 c' $$ [HcmpM HcrevM]
  · iunfold mvcc.muInvAt; iframe HcmpM HcrevM; iframe #; ipureintro; exact HcM
  ihave Hright : mvcc.compactRight γ c' $$ [Hcr Hq]
  · iunfold mvcc.compactRight; iframe Hcr Hq Hlive
  wp_apply (h0 s γ hcmp) $$ [$HRTok] as %pcc HRTok
  · iframe #
  (try wp_auto)
  wp_apply (h1 s γ rev c' P f Pre Q Post log hcmp) $$ [$Hmu1 $Hright $Hcs $HhookW $HRTok] as %ch %prev %err ⟨HRTok, HhookW, Hres⟩
  · iframe #; ipureintro; exact HndC
  (try wp_auto)
  wp_apply (h2 trace te _ slice.nil) $$ [Htrc] as Htrc
  · iframe #; iframe Htrc; iapply traceutil.ownFields_nil
  (try wp_auto)
  icases Hres with (⟨⟨%Herr, %Hch, %Hprev, %Hlt⟩, Hmu, Hright, HPost, #Hjob⟩ |
    ⟨⟨%Hle, %Hprev⟩, ⟨%ec, #Hec, %Herr⟩, Hmu, Hright, HPre, #Hch⟩ |
    ⟨⟨%Hlt, %Hch, %Hprev⟩, ⟨%ef, #Hef, %Herr⟩, #Hcert, Hmu, Hright, HPre⟩)
  · subst Herr
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu Hwr]
    · inext; iunfold mvcc.muInv; iexists (sint.Z rev); iframe Hwr; iexact Hmu
    (try wp_auto)
    iunfold mvcc.compactRight at Hright
    icases Hright with ⟨Hcr, Hq, #Hlive⟩
    wp_apply (h3 s γ trace rev prev pcc te htr) $$ [$Hjob $Hq $Htrc] as %ch' ⟨#Hch', Hq, Htrc⟩
    (try wp_auto)
    iapply HΦ
    iframe Htrc HRTok HhookW
    ileft
    iframe HPost Hch'
    isplitr
    · ipureintro; exact ⟨rfl, Hlt⟩
    isplitl [Hcr Hq]
    · iunfold mvcc.compactRight; iframe Hcr Hq Hlive
    iunfold mvcc.compactJobPreD at Hjob -- Q1 (a)
    icases Hjob with ⟨-, -, -, -, #Hlb, -, -⟩
    iexact Hlb
  · subst Herr
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu Hwr]
    · inext; iunfold mvcc.muInv; iexists c'; iframe Hwr; iexact Hmu
    (try wp_auto)
    iapply HΦ
    iframe Htrc HRTok HhookW
    iright; ileft
    iframe Hright HPre Hch
    isplitr
    · ipureintro; exact Hle
    iexists ec; iframe Hec; ipureintro; rfl
  · subst Herr Hch
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu Hwr]
    · inext; iunfold mvcc.muInv; iexists c'; iframe Hwr; iexact Hmu
    (try wp_auto)
    iapply HΦ
    iframe Htrc HRTok HhookW
    iright; iright
    iframe Hright HPre Hcert
    isplitr
    · ipureintro; exact ⟨Hlt, rfl⟩
    iexists ef; iframe Hef; ipureintro; rfl

theorem mvcc.store.Compact.wp_proofD
    (h0 : mvcc.store.checkPrevCompactionCompleted.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.updateCompactRev.specD (GF := GF) (hG := hG))
    (h2 : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (h3 : mvcc.store.compact.specD (GF := GF) (hG := hG)) :
    mvcc.store.Compact.specD (GF := GF) (hG := hG) := by
  intro s γ trace rev c P f Pre Q Post log te htr hcmp hc
  exact mvcc.store.Compact.wp_of_leD h0 h1 h2 h3 s γ trace rev c P f Pre Q Post log te htr hcmp hc

/-- **The drafted `store.Compact`, linked** (draft of `Results.lean`'s `mvcc_store_Compact`): the
copies above with today's linked callees (`mvcc/Link.lean`). -/
theorem mvcc_store_CompactD [go_etcd_io.etcd.cache.v3.Assumptions] :
    mvcc.store.Compact.specD (GF := GF) (hG := hG) :=
  mvcc.store.Compact.wp_proofD mvcc.store.wp_checkPrevCompactionCompleted
    (mvcc.store.updateCompactRev.wp_proofD schedule.wp_NewJob mvcc.store.wp_compactBarrier
      schedule.Scheduler.wp_Schedule mvcc.wp_SetScheduledCompact)
    traceutil.Trace.wp_Step
    (mvcc.store.compact.wp_proofD schedule.wp_NewJob context.wp_Err mvcc.store.wp_compactBarrier
      (mvcc.store.scheduleCompaction.wp_proofD mvcc.treeIndex.wp_Compact binary.bigEndian.wp_PutUint64
        mvcc.wp_newKVHasher mvcc.wp_BytesToRev mvcc.kvHasher.wp_WriteKeyValue
        mvcc.wp_UnsafeSetFinishedCompact mvcc.kvHasher.wp_Hash zap.wp_Int64 zap.wp_Duration
        zap.wp_Int' zap.wp_Uint32 zap.wp_String go_humanize.wp_Bytes zap.Logger.wp_Info
        mvcc.wp_RevToBytes time.Time.wp_Unix)
      zap.wp_Error zap.Logger.wp_Warn mvcc.hashStorage.wp_Store zap.Logger.wp_Info
      schedule.Scheduler.wp_Schedule traceutil.Trace.wp_Step)

/-- The drafted `compactLockfree`, linked (as `Link.lean`'s `wp_compactLockfree`). -/
theorem mvcc.store.wp_compactLockfreeD [go_etcd_io.etcd.cache.v3.Assumptions] :
    mvcc.store.compactLockfree.specD (GF := GF) (hG := hG) :=
  mvcc.store.compactLockfree.wp_proofD mvcc.store.wp_checkPrevCompactionCompleted
    (mvcc.store.updateCompactRev.wp_proofD schedule.wp_NewJob mvcc.store.wp_compactBarrier
      schedule.Scheduler.wp_Schedule mvcc.wp_SetScheduledCompact)
    traceutil.wp_TODO
    (mvcc.store.compact.wp_proofD schedule.wp_NewJob context.wp_Err mvcc.store.wp_compactBarrier
      (mvcc.store.scheduleCompaction.wp_proofD mvcc.treeIndex.wp_Compact binary.bigEndian.wp_PutUint64
        mvcc.wp_newKVHasher mvcc.wp_BytesToRev mvcc.kvHasher.wp_WriteKeyValue
        mvcc.wp_UnsafeSetFinishedCompact mvcc.kvHasher.wp_Hash zap.wp_Int64 zap.wp_Duration
        zap.wp_Int' zap.wp_Uint32 zap.wp_String go_humanize.wp_Bytes zap.Logger.wp_Info
        mvcc.wp_RevToBytes time.Time.wp_Unix)
      zap.wp_Error zap.Logger.wp_Warn mvcc.hashStorage.wp_Store zap.Logger.wp_Info
      schedule.Scheduler.wp_Schedule traceutil.Trace.wp_Step)

/-! ## The store's creation, drafted -/

/-- **Draft of `NewStore.spec`** (Q1 (a)): the pre loses `mvcc.kbWTSupplyM kb` (the compaction takes
it, `store.Compact.specD`); the rest as today. -/
abbrev mvcc.NewStore.specD : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (wq : Bool) (γi : mvcc.IdxNames) (γok : GName),
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
      ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = kb ∧ γ.watchQ = wq ∧ γ.idx = γi ∧ γ.cok = γok⌝ ∗
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
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗ mvcc.writerFrag γ ∗
      mvcc.crevUB γ.idx (1 : Qp).half (-1) ∗ mvcc.retiredAt γ (mvcc.nJobRd kb) }}

/-- **Draft of the bridge `NewStore_backend`** (`StoreBackend.lean`), over `NewStore.specD`: the
pre loses `kbWTSupplyM (some d)`. -/
theorem mvcc.NewStore_backendD
    (hNewStore : mvcc.NewStore.specD (GF := GF) (hG := hG))
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hbUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hLSR : backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (d : mvcc.KBReal)
    (hP : mvcc.bridgeParams d.P) (γb γl : GName) (Pk : IProp GF) (f : GoFunc)
    (hf : f ≠ func.nil) (rd0 : GoFunc) (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ backend.plHookRO d.γB f ∗
        mvcc.keySized d.γB d.P d.be ∗
        -- (the backend-compaction stage) the deletable-keys registration, unfixed: the store fixes it
        -- by its compaction mode (`dlNoDel`, or the store's deletable keys, `storeDlReg`)
        backend.dlInit d.γB ∗
        -- (question 5's core stage, part (4)) in compaction mode, the compaction keys' values tracked
        -- (the backend's constructor's `fkCl`)
        □ (⌜d.cm = true⌝ -∗ backend.fkV d.γB true) ∗
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
        ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d ∧ γ.watchQ = false⌝ ∗
        mvcc.isStore s γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd) ∗ ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗ mvcc.hookIs γ Pk #f ∗
        (∃ rv wv : Loc,
          s.[store, go!"ReadView"] ↦
            (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv s γ ∗
          s.[store, go!"WriteView"] ↦
            (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
          mvcc.isWriteView wv s γ) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd (some d)) (),
          mvcc.storeReaderC s γ) ∗
        ownToks γ.revs (2 ^ 63 - 5) ∗ mvcc.idxCert γ.idx [[], []] ∗ mvcc.storeCloser s γ ∗
        mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.crevUB γ.idx (1 : Qp).half (-1) ∗
        mvcc.retiredAt γ (mvcc.nJobRd (some d)) }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hhk, #Hsz, Hdl, #Hfv, Hv, Hncmp, Hrg, Hw1, Hw2, Hsrm, Hrts, Hlrd, #Hle, Hro⟩ HΦ
  -- the index's names and the certificate map, fresh (D13a: `NewStore` takes them)
  imod mvcc.idxFresh_alloc (GF := GF) with ⟨%γi, Hifresh⟩
  -- the deletable keys fixed by the mode (question 5's core stage, part (4)): a compacting store's
  -- (`storeDlReg`, over the index's names), and its contract with the compaction (the new bridge);
  -- else nothing deletable (`dlNoDel`) and the old bridge
  ihave Hbk : iprop(|==> □ ∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
      mvcc.storeBackend (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be) s γ Pk) $$ [Hdl]
  · cases hc : d.cm with
    | false =>
      imod backend.dlNoDel_fix d.γB $$ Hdl with #Hnd
      ihave #Hbk := mvcc.storeBackend_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
        hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe d hP hc Pk γb $$ [$Hbpkg $Hsch $Hb $Hsz $Hnd]
      imodintro
      iintro !> %s %γ %hγ
      iapply Hbk
      ipureintro; exact ⟨hγ.1, hγ.2.1⟩
    | true =>
      imod backend.dlReg_fix d.γB _ $$ Hdl with #Hreg
      ihave #Hfv' := Hfv $$ [] 
      · ipureintro; first | exact hc | rfl
      imodintro
      iintro !>
      iapply mvcc.storeBackend_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
        hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP d hP Pk γb γi
      iframe Hbpkg Hsch Hb Hsz Hfv'
      iunfold mvcc.storeDlReg
      iexact Hreg
  imod Hbk with #Hbk
  imod ghost_map_alloc_empty (K := w64) (V := mvcc.Log) (GF := GF) with ⟨%γok, Hok0⟩
  iapply (hNewStore lg _ le cfg (some d) γb γl Pk #f rd0 false γi γok hcfg hrb)
    $$ %Φ [Hv Hncmp Hrg Hw1 Hw2 Hsrm Hrts Hlrd Hro Hifresh Hok0]
  · iframe Hpkg Hle Hro Hifresh Hok0 Hsrm
    isplitr
    · iexact Hbk
    rw [show mvcc.kbView (GF := GF) (some d) γb 1 (∅ : mvcc.Bucket) = mvcc.bkView d.γB 1 ∅ from rfl,
      show mvcc.kbNoCmp (GF := GF) (some d) γb = mvcc.bkNoCmp d.γB from rfl,
      show mvcc.kbRegRight (GF := GF) (some d) = mvcc.lateReg d.gx from rfl,
      show mvcc.kbWT (GF := GF) (some d) = backend.wbTok d.γB from rfl,
      show mvcc.kbRT (GF := GF) (some d) = mvcc.bkRTx d.γB d.P d.be from rfl]
    iframe Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd
  inext
  iintro %s ⟨%γ, %Hγ, Hs, Hro, Hok, #Hh0, Hv, Hr, Ht, Hc, -, Hcl, Hst, -, Hfrag, Hcr, Hret⟩
  ihave Hh := mvcc.hookIs_of_init γ Pk #f d Hγ.2.2.1 f hf $$ [$Hh0 $Hhk $Hfrag]
  iapply HΦ
  iexists γ
  iframe Hs Hro Hok Hh Hv Hr Ht Hc Hcl Hst Hcr Hret
  ipureintro; exact ⟨Hγ.1, Hγ.2.1, Hγ.2.2.1, Hγ.2.2.2.1⟩

/-- **Draft of the export `mvcc_NewStore_backend`** (`Results.lean`), over `NewStore.specD` (a hypothesis
here; linked at the switch): the pre loses `kbWTSupplyM (some d)`. -/
theorem mvcc_NewStore_backendD [go_etcd_io.etcd.cache.v3.Assumptions]
    (hNS : mvcc.NewStore.specD (GF := GF) (hG := hG)) (lg : Loc) (le : GoInterface)
    (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (γb γl : GName) (Pk : IProp GF)
    (f : GoFunc) (hf : f ≠ func.nil) (rd0 : GoFunc) (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ backend.plHookRO d.γB f ∗
        mvcc.keySized d.γB d.P d.be ∗
        -- (the backend-compaction stage) the deletable-keys registration, unfixed: the store fixes it
        -- by its compaction mode (`dlNoDel`, or the store's deletable keys, `storeDlReg`)
        backend.dlInit d.γB ∗
        -- (question 5's core stage, part (4)) in compaction mode, the compaction keys' values tracked
        -- (the backend's constructor's `fkCl`)
        □ (⌜d.cm = true⌝ -∗ backend.fkV d.γB true) ∗
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
        ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d ∧ γ.watchQ = false⌝ ∗
        mvcc.isStore s γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd) ∗ ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗ mvcc.hookIs γ Pk #f ∗
        (∃ rv wv : Loc,
          s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv s γ ∗
          s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"WriteView"] ↦
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.writeView.ty) #wv : GoInterface) ∗
          mvcc.isWriteView wv s γ) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd (some d)) (),
          mvcc.storeReaderC s γ) ∗
        ownToks γ.revs (2 ^ 63 - 5) ∗ mvcc.idxCert γ.idx [[], []] ∗ mvcc.storeCloser s γ ∗
        mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.crevUB γ.idx (1 : Qp).half (-1) }} := by
  iintro %Φ H HΦ
  iapply (mvcc.NewStore_backendD hNS backend.backend.wp_ConcurrentReadTx
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
      lg le cfg d hP γb γl Pk f hf rd0 hcfg hrb) $$ %Φ [H]
  · iexact H
  inext
  iintro %s ⟨%γ, %Hγ, Hs, Hrd, Hcok, Hh, Hv, Hr, Ht, Hc, Hcl, Hfs, Hcr, -⟩
  iapply HΦ
  iexists γ
  iframe Hs Hrd Hcok Hh Hv Hr Ht Hc Hcl Hfs Hcr
  ipureintro; exact Hγ

/-- **Draft of the export `mvcc_NewStore_backend_cmp`** (`Results.lean`), over `NewStore.specD` (a hypothesis
here; linked at the switch): the pre loses `kbWTSupplyM (some d)`. -/
theorem mvcc_NewStore_backend_cmpD [go_etcd_io.etcd.cache.v3.Assumptions]
    (hNS : mvcc.NewStore.specD (GF := GF) (hG := hG)) (lg : Loc) (le : GoInterface)
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
        mvcc.isStore s γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd) ∗ ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗ mvcc.hookIs γ Pk #f ∗
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
        mvcc.compactRight γ (-1) ∗ mvcc.storeStop s γ ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗
        mvcc.retiredAt γ 1 }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hhk, #Hsz, Hdl, #Hfk, Hv, Hncmp, Hrg, Hw1, Hw2, Hsrm,
    Hrts, Hlrd, #Hle, Hro⟩ HΦ
  iapply wp_fupd
  wp_apply (mvcc.NewStore_backendD hNS backend.backend.wp_ConcurrentReadTx
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
  imod mvcc.compactRight_of_closer s γ $$ [Hcl Hright] with ⟨Hcr, #Hstop⟩
  · iframe Hcl Hright
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
