/-
Compaction (`kvstore.go`'s `Compact` and its helpers, `kvstore_compaction.go`, `store.go`'s meta
keys, `index.go`'s and `key_index.go`'s compaction): what the specs of the compaction functions
are stated in. Lean-first (2026-10-13, the mvcc store's unit 5a; `notes/decisions.md`, "mvcc:
compaction"). The pure model is `Compact.lean`; the store's compaction state is in
`InvStore.lean` (`compactMainRev` under `s.mu` and `s.revMu`, `muInv`/`revMuInv`; the
compaction right `compactRightR`, `InvCompact.lean`; the frozen store `crevFrozen`; the keys compaction may delete,
`delKey`; the meta keys' record `metaCompact` and the finished compactions' `compactedAt`, in the
batch lock's resource).

* **The `available` map** (`map[Revision]struct{}`): `availAdd` (`doCompact` adds the revision it
  keeps, `kiAvail`), `keepApply` (`keep`: the same, but not a tombstone that ends a generation
  that is not the last, `kiKeep`); `keepSetIs A log c` (the map `treeIndex.Compact` returns: the
  revisions compaction at `c` keeps of a certified log), `keepOfIs A log rev` (`treeIndex.Keep`'s).
* **The channel `Compact` returns** (`compactChan ch Q`, the caller's receive right; the job holds
  the close right, `compactCloser`): Perennial's broadcast idiom, closed once, a receive returns
  once it is closed with `□ Q`. For a scheduled compaction at `rev`, `Q = compactDone s γ rev`:
  the compaction finished (`compactedAt γ rev`), or it was interrupted — the store's stop
  channel closed (`storeStopped`: `Close`), or the job's context cancelled (the scheduler
  stopped: `Close`/`Restore`, out of scope; the barrier then closes the channel). For
  `ErrCompacted`'s barrier, `Q = True`.
* **The job's context** (`barrierCtx`): `context.TODO()`'s value, or an `isContext` (the
  scheduler's, maybe cancelled).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ### The `available` map -/

section maps
variable [GooseExts]

/-- `doCompact`'s addition to `available` (the revision it keeps, if any). -/
def availAdd (A : GMap Revision Unit) : Option Rev → GMap Revision Unit
  | some r => GMap.insert (revVal r) () A
  | none => A

/-- `keep`'s effect on `available`: nothing for an empty key index; else `doCompact`'s addition,
taken back for a tombstone that ends a generation that is not the last (`kiKeep`). -/
def keepApply (A : GMap Revision Unit) (atRev : w64) (ki : KeyIndex) : GMap Revision Unit :=
  if kiIsEmpty ki then A
  else
    match kiAvail atRev ki with
    | none => A
    | some r =>
      if kiKeep atRev ki = some r then GMap.insert (revVal r) () A
      else GMap.delete (revVal r) (GMap.insert (revVal r) () A)

/-- The generations `doCompact` walks: some, every one but the last with a revision (its
tombstone, `g.revs[len(g.revs)-1]`; the code indexes it). -/
def gensOk (ki : KeyIndex) : Prop :=
  ki.gens ≠ [] ∧ ∀ i, i + 1 < ki.gens.length → (ki.gens.getD i Gen.empty).revs ≠ []

/-- The map `treeIndex.Compact(c)` returns: the revisions compaction at `c` keeps of the log
(`keepAt`), as `Revision` values. -/
def keepSetIs (A : GMap Revision Unit) (log : Log) (c : Int) : Prop :=
  ∀ r : Rev, (A.lookup (revVal r)).isSome ↔ keepAt log c r

/-- The map `treeIndex.Keep(rev)` returns: every key's `kiKeep` at `rev` of the log. -/
def keepOfIs (A : GMap Revision Unit) (log : Log) (rev : w64) : Prop :=
  ∀ r : Rev, (A.lookup (revVal r)).isSome ↔ ∃ k, kiKeep rev (kiOfKey (evsOf log) k) = some r

end maps

section chans
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The store was stopped** (persistent): the stop channel of its scheduler at the names `γ`
(the one the payload's name `γ.sx` records, `stopPayAt`) is closed (`store.Close`,
`store.Restore`; the job's loop receives from it). (M2, the storage side, item 17: until then the
channel was named by the field's `↦□`, which the jobs no longer have: they lease a fraction of
the fields.) -/
def storeStopped (γ : StoreNames) : IProp GF :=
  iprop(∃ (c : Loc) (γc : ChanNames), dghostVar γ.sx DFrac.discard c ∗
    ownBroadcastChan c γc iprop(True) Broadcast.Done)

instance storeStopped_persistent (γ : StoreNames) : Persistent (storeStopped (GF := GF) γ) := by
  unfold storeStopped; infer_instance

/-- **A scheduled compaction at `rev` is done** (persistent; what a receive on `Compact`'s
channel gives): it finished (`compactedAt`), or it was interrupted: the store was stopped, or the
job's context (the scheduler's) was cancelled (both only when the store is closed or restored).
(The store `s` is no longer read since the stop is named by the payload's name, item 17; the
signature is the approved text's.) -/
def compactDone (_s : Loc) (γ : StoreNames) (rev : Int) : IProp GF :=
  iprop(compactedAt γ rev ∨ storeStopped γ ∨
    ∃ cd : context.ContextDesc (IProp GF), context.ContextClosed cd.Done_gn)

/-- **The receive right** on a channel closed once with `Q` (persistent: Perennial's broadcast
idiom). -/
def compactChan (ch : GoChan) (Q : IProp GF) : IProp GF :=
  iprop(∃ γc : ChanNames, ownBroadcastChan ch γc Q Broadcast.Unknown)

instance compactChan_persistent (ch : GoChan) (Q : IProp GF) :
    Persistent (compactChan (GF := GF) ch Q) := by
  unfold compactChan; infer_instance

/-- **The close right** on that channel (the job's, or the barrier's): closing needs `□ Q`. -/
def compactCloser (ch : GoChan) (Q : IProp GF) : IProp GF :=
  iprop(∃ γc : ChanNames, ownBroadcastChan ch γc Q Broadcast.Pending)

/-- The context a compaction job or barrier runs with: `context.TODO()`'s value (after a failed
pass, the job's barrier), or an `isContext` (the scheduler's: maybe cancelled). -/
def barrierCtx (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(⌜ctx = todoCtxV⌝ ∨ context.isContext ctx cd)

instance barrierCtx_persistent (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (barrierCtx (GF := GF) ctx cd) := by
  unfold barrierCtx; infer_instance

/-- **A compaction at `c` deletes fewer than `2 ^ 62` keys** (a physical bound, as the server's
`storeSmall`; item 8, 2026-10-17): the log up to revision `c` has fewer than `2 ^ 62` changes.
The keys a compaction deletes are distinct bucket keys of those changes, so `scheduleCompaction`'s
count of them, an `int`, never wraps, and `dbCompactionKeysCounter.Add(float64(count))` gets a
non-negative value (prometheus' `counter.Add` panics on a negative one). Not a premise since
2026-10-18 (D19b): a certified log's changes are fewer than the time receipts' bound
(`idxCert`), at most `2 ^ 48` (`isStore`), so `CompactSmall_of_cert`. -/
def CompactSmall (log : Log) (c : Int) : Prop :=
  ((log.take (c.toNat + 1)).map List.length).sum < 2 ^ 62

/-- A log with fewer than `2 ^ 62` changes is small at every revision. -/
theorem CompactSmall_of_logCh {log : Log} (c : Int) (h : logCh log < 2 ^ 62) :
    CompactSmall log c := by
  unfold CompactSmall
  suffices hle : ∀ (l : Log) (n : Nat), ((l.take n).map List.length).sum ≤ logCh l by
    have := hle log (c.toNat + 1); omega
  intro l
  induction l with
  | nil => intro n; simp [logCh]
  | cons cs l ih =>
    intro n
    cases n with
    | zero => simp
    | succ n => have := ih n; simp [logCh] at *; omega

/-- **A certified log is small at every revision** (D19b): its changes are fewer than the time
receipts' bound (`idxCert`), at most `2 ^ 48` (`isStore`). -/
theorem CompactSmall_of_cert (s : Loc) (γ : StoreNames) (log : Log) (c : Int) :
    isStore (GF := GF) s γ ∗ idxCert γ.idx log ⊢ ⌜CompactSmall log c⌝ := by
  iintro ⟨Hs, Hc⟩
  iunfold isStore at Hs
  iNamed Hs
  iunfold idxCert at Hc
  icases Hc with ⟨-, -, -, %Hlt⟩
  ipureintro
  exact CompactSmall_of_logCh c (by have : (2 : Nat) ^ 48 < 2 ^ 62 := by decide
                                    omega)

/-! ### The jobs' share of the fields, leased (M2, the storage side: the approval's item 17)

The compaction jobs read the four fields `store.Restore` writes (`s.b`, `s.kvindex`, `s.stopc`;
`scheduleCompaction`, `compactBarrier`) without the store's locks, and `store.Restore`/`store.Close`
take them back after `fifoSched.Stop()`, which returns once no job runs or will run
(`schedule.go:150-184`). Loads are not atomic (`GoLoad` is `StartRead` then `FinishRead`), so a
job cannot read through an invariant opened per load: it holds a fraction of the fields for its
whole run. **The lease** (repair (b) of `notes/decisions.md`, "M2's storage side: the compaction
chain over the restorable right is not provable as drafted"; the coordinating agent's choice of
an internal predicate design): the invariant `jobFieldsInv` is in one of three states, *free*
(an eighth of the fields at the objects `o` and the lease token), *leased* (half the scheduler's
run token: a job runs), or *reclaimed* (the whole run token: the stopper has the eighth). A job
starts with the run token (`schedule.jobFnSpec`): it takes the eighth and the lease token out,
leaving half its run token (`storeStopR_lease`), and at its end puts them back and takes its half
(`jobLease_return`). The stopper, once `Stop` has returned the run token (`schedDone`), finds the
invariant free (leased or reclaimed would make the run token more than whole) and takes the eighth
(`storeStopR_reclaim`). Nobody else can change the state: the free state needs the lease token,
the other two the run token's fractions, which the running job or the stopper holds. -/

/-- The jobs' invariant's name. -/
abbrev jobFieldsN : Namespace := nroot.@"mvcc_jobFields"

/-- An eighth (the closer's quarter, halved). -/
abbrev q8 : Qp := (1 : Qp).half.half.half

/-- `q8 + q8` is the closer's quarter. -/
theorem q8_add : q8 + q8 = (1 : Qp).half.half := Qp.half_add_half _

/-- **The jobs' invariant's three states** (`gl` the lease token's name): free, leased (half the
run token), reclaimed (the run token). -/
def jobFieldsInv (s : Loc) (γ : StoreNames) (o : StoreObjs) (gl : GName) : IProp GF :=
  iprop((fieldShareAt s γ q8 o ∗ dghostVar gl (DFrac.own 1) ()) ∨
    dghostVar γ.sch.run (DFrac.own (1 : Qp).half) () ∨ schedule.schedDone γ.sch)

/-- **The compaction jobs' share of the fields at the objects `o`** (persistent; the approval's
item 17, with the lease): the jobs' invariant. A running job leases the eighth for its run
(`storeStopR_lease`, `jobLease_return`); the stopper reclaims it after `Stop`
(`storeStopR_reclaim`). The objects are fixed in the invariant: while the eighth is in it or
leased, no one writes the fields (`store.Restore` holds every other share and takes this one
only after `Stop`, then moves to fresh names). -/
@[no_expose] def storeStopR (s : Loc) (γ : StoreNames) (o : StoreObjs) : IProp GF :=
  iprop((∃ gl : GName, inv jobFieldsN (jobFieldsInv s γ o gl)) ∗ isStopChan o.sstop)

instance storeStopR_persistent (s : Loc) (γ : StoreNames) (o : StoreObjs) :
    Persistent (storeStopR (GF := GF) s γ o) := by
  unfold storeStopR; infer_instance

/-- **A running job's lease** (exclusive): the lease token, half the run token (the other half
in the invariant, leased) and the worker's thread token, with the invariant. -/
def jobLease (s : Loc) (γ : StoreNames) (o : StoreObjs) : IProp GF :=
  iprop(∃ gl : GName, inv jobFieldsN (jobFieldsInv s γ o gl) ∗ dghostVar gl (DFrac.own 1) () ∗
    dghostVar γ.sch.run (DFrac.own (1 : Qp).half) () ∗ threadTok)

/-- Half the run token and the whole one are too much. -/
theorem run_half_whole (γs : schedule.SchedNames) :
    dghostVar (GF := GF) γs.run (DFrac.own (1 : Qp).half) () ∗ dghostVar γs.run (DFrac.own 1) () ⊢
      False := by
  iintro ⟨H1, H2⟩
  icombine H2 H1 gives %Hv
  obtain ⟨Hv, -⟩ := Hv
  exact absurd (DFrac.valid_own.1 Hv) (Qp_one_add_not_le _)

/-- **The jobs' share, made** (the right's construction, `compactRightR_of_closer`): an eighth of
the fields at `o`, the invariant free. -/
theorem storeStopR_alloc (s : Loc) (γ : StoreNames) (o : StoreObjs) (E : CoPset) :
    ⊢ fieldShareAt (GF := GF) s γ q8 o -∗ isStopChan o.sstop ={E}=∗ storeStopR s γ o := by
  iintro Hf #Hsc
  imod dghostVar_alloc (GF := GF) () with ⟨%gl, Hgl⟩
  imod inv_alloc jobFieldsN E (jobFieldsInv s γ o gl) $$ [Hf Hgl] with #Hi
  · inext; iunfold jobFieldsInv; ileft; iframe Hf Hgl
  imodintro
  iunfold storeStopR
  iframe Hsc
  iexists gl
  iexact Hi

/-- The jobs' share names the objects' stop channel (the job's loop receives from it). -/
theorem storeStopR_stopChan (s : Loc) (γ : StoreNames) (o : StoreObjs) :
    storeStopR (GF := GF) s γ o ⊢ isStopChan o.sstop := by
  iintro H
  iunfold storeStopR at H
  icases H with ⟨-, #Hsc⟩
  iexact Hsc

/-- **A job takes the lease** (at its start, with the run token): the eighth of the fields at `o`
and the lease, the invariant leased. -/
theorem storeStopR_lease (s : Loc) (γ : StoreNames) (o : StoreObjs) :
    ⊢ storeStopR (GF := GF) s γ o -∗ schedule.schedRunning γ.sch -∗ £ 1 ={⊤}=∗
      fieldShareAt s γ q8 o ∗ jobLease s γ o := by
  iintro #Hi Hrun Hlc
  iunfold storeStopR at Hi
  icases Hi with ⟨⟨%gl, #Hi⟩, -⟩
  iunfold schedule.schedRunning at Hrun
  icases Hrun with ⟨Hrun, Htt⟩
  iinv Hi with Hb Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑jobFieldsN) $$ Hlc Hb with Hb
  iunfold jobFieldsInv at Hb
  icases Hb with (⟨Hf, Hgl⟩ | Hh | Hd)
  · ihave Hsp := dghostVar_split γ.sch.run () (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
      $$ [Hrun]
    · rw [← dfrac_own_half_half 1]; iexact Hrun
    icases Hsp with ⟨Hr1, Hr2⟩
    imod Hclose $$ [Hr1] with -
    · inext; iunfold jobFieldsInv; iright; ileft; iexact Hr1
    imodintro
    iframe Hf
    iunfold jobLease
    iexists gl
    iframe Hi Hgl Hr2 Htt
  · iexfalso
    iapply run_half_whole γ.sch $$ [$Hh $Hrun]
  · iexfalso
    iapply schedule.schedDone_excl γ.sch $$ [Hd Hrun]
    iframe Hd
    iunfold schedule.schedDone
    iexact Hrun

/-- **A job returns the lease** (at its end): the eighth back in the invariant, the run token
whole. -/
theorem jobLease_return (s : Loc) (γ : StoreNames) (o : StoreObjs) :
    ⊢ jobLease (GF := GF) s γ o -∗ fieldShareAt s γ q8 o -∗ £ 1 ={⊤}=∗ schedule.schedRunning γ.sch := by
  iintro Hl Hf Hlc
  iunfold jobLease at Hl
  icases Hl with ⟨%gl, #Hi, Hgl, Hr2, Htt⟩
  iinv Hi with Hb Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑jobFieldsN) $$ Hlc Hb with Hb
  iunfold jobFieldsInv at Hb
  icases Hb with (⟨-, Hgl'⟩ | Hr1 | Hd)
  · iexfalso
    icombine Hgl Hgl' gives %Hv
    obtain ⟨Hv, -⟩ := Hv
    exact absurd (DFrac.valid_own.1 Hv) (Qp_one_add_not_le 1)
  · imod Hclose $$ [Hf Hgl] with -
    · inext; iunfold jobFieldsInv; ileft; iframe Hf Hgl
    imodintro
    iunfold schedule.schedRunning
    iframe Htt
    have h := ((dghostVar_fractional (GF := GF) γ.sch.run ()).fractional (1 : Qp).half
      (1 : Qp).half).2
    rw [Qp.half_add_half] at h
    iapply h
    iframe Hr1 Hr2
  · iexfalso
    iapply run_half_whole γ.sch $$ [$Hr2 Hd]
    iunfold schedule.schedDone at Hd
    iexact Hd

/-- **The jobs' share back** (`Restore`/`Close`, after `Stop`): with the run token, the eighth (the
invariant reclaimed). -/
theorem storeStopR_reclaim (s : Loc) (γ : StoreNames) (o : StoreObjs) :
    ⊢ storeStopR (GF := GF) s γ o -∗ schedule.schedDone γ.sch -∗ £ 1 ={⊤}=∗
      fieldShareAt s γ q8 o := by
  iintro #Hi Hd Hlc
  iunfold storeStopR at Hi
  icases Hi with ⟨⟨%gl, #Hi⟩, -⟩
  iinv Hi with Hb Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑jobFieldsN) $$ Hlc Hb with Hb
  iunfold jobFieldsInv at Hb
  icases Hb with (⟨Hf, -⟩ | Hh | Hd')
  · imod Hclose $$ [Hd] with -
    · inext; iunfold jobFieldsInv; iright; iright; iexact Hd
    imodintro
    iexact Hf
  · iexfalso
    iapply run_half_whole γ.sch $$ [$Hh Hd]
    iunfold schedule.schedDone at Hd
    iexact Hd
  · iexfalso
    iapply schedule.schedDone_excl γ.sch $$ [$Hd $Hd']

/-! ### The compaction right that survives `Restore` and `Close` (the approval's items 17, 23, 24) -/

/-- **The closer's half kept by a compacting store**: an eighth of the fields at the objects `o`,
the stop channel and its close, the scheduler's stop token (`storeCloser` with an eighth in place
of the quarter and without the queue, which the right holds at its revision). -/
@[no_expose] def storeCloserR (s : Loc) (γ : StoreNames) (o : StoreObjs) : IProp GF :=
  iprop(fieldShareAt s γ q8 o ∗ isStopChan o.sstop ∗ stopCloser o.sstop ∗ schedule.schedStopTok γ.sch)

/-- **The compaction right at `c`, restorable** (the approval's item 17; in place of step 1's
`compactRight`, which discarded the closer): the compaction revision's half of the authority, the
jobs' queue at `c`, the closer's half (`storeCloserR`) and the jobs' share of the fields
(`storeStopR`), at the same objects. Nothing is discarded, so `store.Close` (and, in compaction
mode, `store.Restore`) take it back. -/
@[no_expose] def compactRightR (s : Loc) (γ : StoreNames) (c : Int) : IProp GF :=
  iprop(crevUB γ.idx (1 : Qp).half c ∗ compactQueue γ c ∗
    ∃ o : StoreObjs, storeCloserR s γ o ∗ storeStopR s γ o)

/-- **The right, opened** (for the store's own proofs: `store.Compact`'s chain and `store.Close`). -/
theorem compactRightR_iff (s : Loc) (γ : StoreNames) (c : Int) :
    compactRightR (GF := GF) s γ c ⊣⊢
      crevUB γ.idx (1 : Qp).half c ∗ compactQueue γ c ∗
        ∃ o : StoreObjs, (fieldShareAt s γ q8 o ∗ isStopChan o.sstop ∗ stopCloser o.sstop ∗
          schedule.schedStopTok γ.sch) ∗ storeStopR s γ o := by
  unfold compactRightR storeCloserR; exact .rfl

/-- **The right's queue and the closer's eighth of the fields, lent** (`store.Compact`'s chain: the
eighth reads `s.b` and `s.fifoSched`, the queue schedules the job), and the right back from them. -/
theorem compactRightR_take (s : Loc) (γ : StoreNames) (c : Int) :
    compactRightR (GF := GF) s γ c ⊢ ∃ o : StoreObjs, fieldShareAt s γ q8 o ∗ compactQueue γ c ∗
      (fieldShareAt s γ q8 o -∗ compactQueue γ c -∗ compactRightR s γ c) := by
  iintro H
  icases (compactRightR_iff s γ c).1 $$ H with ⟨Hcr, Hq, %o, ⟨Hf, #Hsc, Hstc, Htok⟩, #Hstop⟩
  iexists o
  iframe Hf Hq
  iintro Hf Hq
  iapply (compactRightR_iff s γ c).2
  iframe Hcr Hq
  iexists o
  iframe Hf Hsc Hstc Htok Hstop

/-- **The right's half of the compaction revision's authority, lent** (`store.Compact` agrees it
with `s.mu`'s). -/
theorem compactRightR_crev (s : Loc) (γ : StoreNames) (c : Int) :
    compactRightR (GF := GF) s γ c ⊢ crevUB γ.idx (1 : Qp).half c ∗
      (crevUB γ.idx (1 : Qp).half c -∗ compactRightR s γ c) := by
  iintro H
  icases (compactRightR_iff s γ c).1 $$ H with ⟨Hcr, Hq, Ho⟩
  iframe Hcr
  iintro Hcr
  iapply (compactRightR_iff s γ c).2
  iframe Hcr Hq Ho

/-- **The right from the closer** (in place of step 1's `compactRight_of_closer`, which
discarded): the closer's quarter split, one eighth into the jobs' invariant; the stop token and
the stop channel's close kept. -/
theorem compactRightR_of_closer (s : Loc) (γ : StoreNames) (E : CoPset) :
    ⊢ storeCloser (GF := GF) s γ -∗ crevUB γ.idx (1 : Qp).half (-1) ={E}=∗
      compactRightR s γ (-1) := by
  iintro Hcl Hcu
  iunfold storeCloser at Hcl
  icases Hcl with ⟨%o, Hf, #Hsc, Hstc, Htok, Hq⟩
  have hs := (fieldShareAt_split (GF := GF) s γ q8 q8 o).1
  rw [q8_add] at hs
  icases hs $$ Hf with ⟨Hf1, Hf2⟩
  imod storeStopR_alloc s γ o E $$ Hf2 Hsc with #Hi
  imodintro
  iapply (compactRightR_iff s γ (-1)).2
  iframe Hcu Hq
  iexists o
  iframe Hf1 Hsc Hstc Htok Hi

/-- **The closer's quarter again** (`Restore` after `Stop`): the closer's eighth and the jobs'
eighth, reclaimed with the run token, are at the same objects and make the quarter `storeCloser`
holds. -/
theorem fieldShare_reclaim (s : Loc) (γ : StoreNames) (o : StoreObjs) :
    ⊢ fieldShareAt (GF := GF) s γ q8 o -∗ storeStopR s γ o -∗
      schedule.schedDone γ.sch -∗ £ 1 ={⊤}=∗ fieldShareAt s γ (1 : Qp).half.half o := by
  iintro Hf #Hi Hd Hlc
  imod storeStopR_reclaim s γ o $$ Hi Hd Hlc with Hf'
  have hs := (fieldShareAt_split (GF := GF) s γ q8 q8 o).2
  rw [q8_add] at hs
  imodintro
  iapply hs
  iframe Hf Hf'

/-- **The store's right to close, by the mode** (the approval's item 23, as drafted: the mode of
the backend instance, `kbCmpM γ.kb`, which `physOk`'s tie makes the logical `γ.cm` under a share
of the fields; renamed from `restoreRightPostM`, review round 4's S4: it is `store.Restore`'s
drafted post and `store.Close`'s pre): off, the closer; on, the restorable compaction right at
the store's compaction revision `c` (after a restore, at the new names and the restored revision,
its queue holding the job `restore()` resumed, if any). -/
def storeCloserM (s : Loc) (γ : StoreNames) (c : Int) : IProp GF :=
  if kbCmpM γ.kb then compactRightR s γ c else storeCloser s γ

theorem storeCloserM_off (s : Loc) (γ : StoreNames) (c : Int) (h : ¬ kbCmpM γ.kb) :
    storeCloserM (GF := GF) s γ c ⊣⊢ storeCloser s γ := by
  unfold storeCloserM; simp only [h, ↓reduceIte]; exact .rfl

theorem storeCloserM_on (s : Loc) (γ : StoreNames) (c : Int) (h : kbCmpM γ.kb) :
    storeCloserM (GF := GF) s γ c ⊣⊢ compactRightR s γ c := by
  unfold storeCloserM; simp only [h, ↓reduceIte]; exact .rfl

/-- **A share of the fields, for reading them** (the compaction's functions): the four points-to
at the fraction, what the objects are, and the share back from them. -/
theorem fieldShareAt_acc (s : Loc) (γ : StoreNames) (q : Qp) (o : StoreObjs) :
    fieldShareAt (GF := GF) s γ q o ⊢ storeFields s o (DFrac.own q) ∗ □ physOk s γ o ∗
      (storeFields s o (DFrac.own q) -∗ fieldShareAt s γ q o) := by
  iintro H
  iunfold fieldShareAt at H
  iNamed H
  iframe Hflds Hph
  iintro Hflds
  iunfold fieldShareAt
  simp only [named]
  iframe Hcur Hflds Hfrst Hph

/-- **What `store.Close` uses of the right to close, in either mode**: a share of the fields at the
current objects (to read `s.stopc` and `s.fifoSched`), the stop channel's close, the scheduler's
stop token and the jobs' queue (what `Scheduler.Stop` takes). -/
theorem storeCloserM_close (s : Loc) (γ : StoreNames) (c : Int) :
    storeCloserM (GF := GF) s γ c ⊢ ∃ (o : StoreObjs) (q : Qp) (c' : Int), fieldShareAt s γ q o ∗
      stopCloser o.sstop ∗ schedule.schedStopTok γ.sch ∗ compactQueue γ c' := by
  iintro H
  by_cases hm : kbCmpM γ.kb
  · icases (storeCloserM_on s γ c hm).1 $$ H with H
    icases (compactRightR_iff s γ c).1 $$ H with ⟨-, Hq, %o, ⟨Hf, -, Hstc, Htok⟩, -⟩
    iexists o, q8, c
    iframe Hf Hstc Htok Hq
  · icases (storeCloserM_off s γ c hm).1 $$ H with H
    iunfold storeCloser at H
    icases H with ⟨%o, Hf, -, Hstc, Htok, Hq⟩
    iexists o, (1 : Qp).half.half, (-1)
    iframe Hf Hstc Htok Hq

/-- **What the compaction job at `rev` needs** (persistent): the store, the jobs' share of its
fields at some objects (`storeStopR`: the job leases it for its run; the approval's item 17, in
place of step 1's discarded `storeStop` and the never-stopped scheduler `schedLive`: the barriers
are tracked), its backend supporting the compaction (`storeCmp`), a lower bound `rev` of the
compaction revision (`Compact` set it), a certified log with revision `rev`, which does not delete a
key and put it again (`NoDelPutAt`: `store.Compact`'s caller asserted it; the keys the job deletes
carry it, `delKey`; 2026-10-13, unit 6a), with the index's count of its events (`idxNevLb`: D22
receiver epochs, S1). (Until 2026-10-18 also `CompactSmall` at `rev`, the caller's physical bound;
now the job derives it, `CompactSmall_of_cert`.) And (M2, the storage side, Q1 (a), 2026-10-30) the
write-back supply (`kbWTSupplyM γ.kb`, persistent), which `store.Compact`'s caller gave and the
job's write sessions spend. -/
def compactJobPre (s : Loc) (γ : StoreNames) (rev : w64) : IProp GF :=
  iprop(isStore s γ ∗ (∃ o : StoreObjs, storeStopR s γ o) ∗ ⌜storeCmp γ⌝ ∗
    crevLb γ.idx (sint.Z rev) ∗ kbWTSupplyM γ.kb ∗
    ∃ log : Log, idxCert γ.idx log ∗ idxNevLb γ.idx log ∗
      ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length ∧ NoDelPutAt log (sint.Z rev)⌝)

instance compactJobPre_persistent (s : Loc) (γ : StoreNames) (rev : w64) :
    Persistent (compactJobPre (GF := GF) s γ rev) := by
  unfold compactJobPre; infer_instance

end chans

end mvcc
end EtcdGrove
end Perennial
