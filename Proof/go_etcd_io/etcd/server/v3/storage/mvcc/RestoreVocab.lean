/-
**The vocabulary of `store.Restore`'s spec in either mode** (M2's item 15, step A3;
`notes/m2-storage-plan.md`, "Step 2: restore in compaction mode"): what `Restore` takes of the
store's right (`restoreRightM`), the received backend's image (`restoreImageM`) with its records
(`kbRecs`, over the merged compaction-key ghost `backend.fkVD`), the new backend's deletable keys
(`restoreRegM`/`restoreFixM`), the backend's contract with the records (`storeBackendTR`) and
the restored log's receipt (`restoreRcptM`). Moved here from the step's Drafts
(`M2StorageDraftRestore`, `M2StorageDraftSealed`) when the spec switched.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InstanceLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CmpRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreCut
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndexRestore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **What `Restore` takes of the store's right, by the mode** (`store.Restore`'s pre): off, today's closer and the frozen revision, at `c = -1`;
on, the restorable compaction right at the store's compaction revision `c`. -/
def mvcc.restoreRightM (s : Loc) (γ : mvcc.StoreNames) (c : Int) : IProp GF :=
  if mvcc.kbCmpM γ.kb then mvcc.compactRightR s γ c
  else iprop(mvcc.storeCloser s γ ∗ mvcc.crevFrozen γ ∗ ⌜c = -1⌝)

theorem mvcc.restoreRightM_off (s : Loc) (γ : mvcc.StoreNames) (c : Int)
    (h : ¬ mvcc.kbCmpM γ.kb) :
    mvcc.restoreRightM (GF := GF) s γ c ⊣⊢
      mvcc.storeCloser s γ ∗ mvcc.crevFrozen γ ∗ ⌜c = -1⌝ := by
  unfold mvcc.restoreRightM; simp only [h, ↓reduceIte]; exact .rfl

theorem mvcc.restoreRightM_on (s : Loc) (γ : mvcc.StoreNames) (c : Int)
    (h : mvcc.kbCmpM γ.kb) :
    mvcc.restoreRightM (GF := GF) s γ c ⊣⊢ mvcc.compactRightR s γ c := by
  unfold mvcc.restoreRightM; simp only [h, ↓reduceIte]; exact .rfl

/-- The bytes stored at a record (`RevToBytes(Revision{Main: x})`). -/
def mvcc.recBytes (x : Option w64) : Option GoString := x.map (fun x => mvcc.revBytes ⟨x, W64 0⟩ false)

/-- **The backend's compaction-key ghost, merged** (review round 4's S4: one name `γ.fkv`
at one type, in place of today's `fkV γ w` and round 3's `fkOpenD` beside it at another type): the
well-formedness bit `w` and the client's flag `n` at the open over data whose compaction keys hold
`v`. At the switch `OpenBackend`/`New` over bbolt's `D` give it at
`(fkWInit P D, fkInit D, (dget D meta fin, dget D meta sched))` beside the client's half of the flag,
a put of a compaction key raises the flag strictly (`fkPut`: `f` to `f + 1`), and the batch lock's
and the readers' clause (`fkOk`) gains `f = n → the state's keys are v`: so while the client holds
its half at `n`, every read of the keys returns `v` (`metaReadSpecR`). Rests on bbolt's data as the
backend's proofs already read it (no new axiom expected). -/
def backend.fkVD (γ : backend.BNames) (w : Bool) (n : Nat) (v : Option GoString × Option GoString) :
    IProp GF :=
  dghostVar γ.fkv DFrac.discard (w, n, v)

instance backend.fkVD_persistent (γ : backend.BNames) (w : Bool) (n : Nat)
    (v : Option GoString × Option GoString) : Persistent (backend.fkVD (GF := GF) γ w n v) := by
  unfold backend.fkVD; infer_instance

/-- **Today's `fkV γ w`, over the merged ghost** (the bit alone). -/
def backend.fkVM (γ : backend.BNames) (w : Bool) : IProp GF :=
  iprop(∃ (n : Nat) (v : Option GoString × Option GoString), backend.fkVD γ w n v)

/-- **The compaction keys as opened** (persistent): the client's flag stood at `n` when the
backend was opened over data whose two compaction keys hold `v` (finished, scheduled). -/
def backend.fkOpenD (γ : backend.BNames) (n : Nat) (v : Option GoString × Option GoString) :
    IProp GF :=
  iprop(∃ w : Bool, backend.fkVD γ w n v)

instance backend.fkOpenD_persistent (γ : backend.BNames) (n : Nat)
    (v : Option GoString × Option GoString) : Persistent (backend.fkOpenD (GF := GF) γ n v) := by
  unfold backend.fkOpenD; infer_instance

/-- **The records of the instance `kb`, with the right to write them** (generalizes
`kbNoCmp`, which is its value at no record, `kbRecs_empty`): for the real backend, the client's
half of its compaction-key flag at the value it had when opened over records `r`. It is the
compaction-key write right (`kbRecs_MW`: a compacting store's `mwInv` keeps it, `restore()`'s
resumed `updateCompactRev` writes through it) and, held unmoved, the license to read the records
(`metaReadSpecR`). mvcc's assumed backend has no records vocabulary: only `r = empty`. -/
def mvcc.kbRecs (kb : Option mvcc.KBReal) (γb : GName) (r : mvcc.CmpRecs) : IProp GF :=
  if r = mvcc.CmpRecs.empty then mvcc.kbNoCmp kb γb
  else match kb with
    | none => iprop(False)
    | some d => iprop(∃ n : Nat, backend.fkOwn d.γB n ∗
        backend.fkOpenD d.γB n (mvcc.recBytes r.fin, mvcc.recBytes r.sched))

/-- No record is today's no-compaction token. -/
theorem mvcc.kbRecs_empty (kb : Option mvcc.KBReal) (γb : GName) :
    mvcc.kbRecs (GF := GF) kb γb mvcc.CmpRecs.empty = mvcc.kbNoCmp kb γb := by
  unfold mvcc.kbRecs; simp

/-- **The records are the write right** (`restore` gives it back as `kbMW`, as today's
`kbNoCmp_MW`). -/
theorem mvcc.kbRecs_MW (kb : Option mvcc.KBReal) (γb : GName) (r : mvcc.CmpRecs) :
    mvcc.kbRecs (GF := GF) kb γb r ⊢ mvcc.kbMW kb γb := by
  unfold mvcc.kbRecs
  split
  · exact mvcc.kbNoCmp_MW kb γb
  · cases kb with
    | none => iintro H; iexfalso; iexact H
    | some d =>
      unfold mvcc.kbMW
      iintro ⟨%n, H, -⟩
      iexists n
      iexact H

/-- **`storeBackendT` with the records**: `NC` the records' `kbRecs … r`. -/
def mvcc.storeBackendTR (b : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF)
    (r : mvcc.CmpRecs) : IProp GF :=
  mvcc.isKeyBackendGR b (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ)
    (mvcc.kbRecs γ.kb γ.bucket r) r (mvcc.storePutOk γ) (mvcc.delKey γ) (mvcc.storeW s γ)
    (mvcc.kbWi γ.kb) iprop(True) (mvcc.storeCmp γ) P (mvcc.hookFn γ) (mvcc.storeReq γ) (mvcc.storeRb γ)
    (mvcc.storeBt γ) (mvcc.kbSR γ.kb) (mvcc.kbSRh γ.kb) (mvcc.kbMW γ.kb γ.bucket) (mvcc.kbHookNil γ.kb)

theorem mvcc.storeBackendTR_empty (b : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) :
    mvcc.storeBackendTR (GF := GF) b s γ P mvcc.CmpRecs.empty = mvcc.storeBackendT b s γ P := by
  unfold mvcc.storeBackendTR mvcc.storeBackendT
  rw [mvcc.kbRecs_empty, mvcc.isKeyBackendGR_empty]

/-- **The new backend's deletable keys, unfixed, by the mode** (item 30's D1 repair,
2026-10-30): on, the creator's registration not yet fixed (`dlInit`, as `NewStore` takes it):
`Restore` lends it to `restore()`'s clean read (with the reader's token), then fixes it to the
store's deletable keys (`storeDlReg`, `dlReg_fix`) for the contract; off, nothing (the caller fixed
`dlNoDel`, today's). -/
def mvcc.restoreRegM (d' : mvcc.KBReal) : IProp GF :=
  if d'.cm = true then backend.dlInit d'.γB else iprop(True)

/-- What the contract of the new backend needs fixed, by the mode: on, the store's deletable keys
registered (`storeDlReg`, at the new names' index); off, nothing. -/
def mvcc.restoreFixM (d' : mvcc.KBReal) (γ : mvcc.StoreNames) : IProp GF :=
  if d'.cm = true then mvcc.storeDlReg d'.γB γ.idx else iprop(True)

theorem mvcc.restoreRegM_off (d' : mvcc.KBReal) (h : d'.cm = false) :
    mvcc.restoreRegM (GF := GF) d' = iprop(True) := by
  unfold mvcc.restoreRegM; simp [h]

theorem mvcc.restoreFixM_off (d' : mvcc.KBReal) (h : d'.cm = false) (γ : mvcc.StoreNames) :
    mvcc.restoreFixM (GF := GF) d' γ = iprop(True) := by
  unfold mvcc.restoreFixM; simp [h]

/-- On, the registration fixed gives what the contract needs. -/
theorem mvcc.restoreRegM_fix (d' : mvcc.KBReal) (γ : mvcc.StoreNames) :
    mvcc.restoreRegM (GF := GF) d' ⊢ |==> □ mvcc.restoreFixM d' γ := by
  unfold mvcc.restoreRegM mvcc.restoreFixM
  cases d'.cm with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; iintro -; imodintro; iintro !>; itrivial
  | true =>
    simp only [↓reduceIte]
    iintro H
    imod mvcc.storeDlReg_fix d'.γB γ.idx $$ H with #Hr
    imodintro
    iintro !>
    iexact Hr

/-- **The received backend's image, by the mode** (until item 15, the
pre's `kbViewC (some d') γb' 1 (bucketMap L') ∗ kbNoCmp (some d') γb'`): off, the whole `Key`
bucket at the log `L'` and no record; on, a view of the image's entries `ents` of the job's shape
at the records' revision `r.crev`, the records with the write right (`kbRecs`: the client's half of
the compaction-key flag, which the walk holds from `OpenBackend`'s `fkCl`), the compaction keys
well formed (`fkVM`, the merged ghost), and the image's pure facts. -/
def mvcc.restoreImageM (d' : mvcc.KBReal) (γb' : GName) (L : mvcc.Log) (r : mvcc.CmpRecs) :
    IProp GF :=
  if d'.cm then
    iprop(∃ ents : List mvcc.KvEnt, mvcc.kbViewC (some d') γb' 1 (mvcc.bucketOfEnts ents) ∗
      mvcc.kbRecs (some d') γb' r ∗ backend.fkVM d'.γB true ∗
      ⌜mvcc.recsOk L r ∧ mvcc.recsPos r ∧ mvcc.entsCutAt L r.crev ents ∧ mvcc.NoDelPutAt L r.crev⌝)
  else iprop(mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap L) ∗ mvcc.kbNoCmp (some d') γb' ∗
    ⌜r = mvcc.CmpRecs.empty⌝)

theorem mvcc.restoreImageM_off (d' : mvcc.KBReal) (γb' : GName) (L : mvcc.Log) (r : mvcc.CmpRecs)
    (h : d'.cm = false) :
    mvcc.restoreImageM (GF := GF) d' γb' L r ⊣⊢
      mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap L) ∗ mvcc.kbNoCmp (some d') γb' ∗
        ⌜r = mvcc.CmpRecs.empty⌝ := by
  unfold mvcc.restoreImageM; simp only [h, Bool.false_eq_true, ↓reduceIte]; exact .rfl

/-- **The restored log's persistent receipt, by the mode**: on, `⧖ (logCh L)`, the image's (some member's sealed log, `dbImageR`); off,
nothing (the rebuild's receipts are the writer's, as today). -/
def mvcc.restoreRcptM (d' : mvcc.KBReal) (L : mvcc.Log) : IProp GF :=
  if d'.cm then iprop(⧖ (mvcc.logCh L)) else iprop(True)

instance mvcc.restoreRcptM_persistent (d' : mvcc.KBReal) (L : mvcc.Log) :
    Persistent (mvcc.restoreRcptM (GF := GF) d' L) := by
  unfold mvcc.restoreRcptM; split <;> infer_instance

/-- On, the receipt is the restored writer's (`idxWriter_split`'s right-to-left). -/
theorem mvcc.restoreRcptM_on (d' : mvcc.KBReal) (L : mvcc.Log) (h : d'.cm = true) :
    mvcc.restoreRcptM (GF := GF) d' L ⊣⊢ ⧖ (mvcc.logCh L) := by
  unfold mvcc.restoreRcptM; simp only [h, ↓reduceIte]; exact .rfl

/-- Off, the old job's budgets are nothing. -/
theorem mvcc.compactJobResM_off (kb : Option mvcc.KBReal) (h : ¬ mvcc.kbCmpM kb) :
    mvcc.compactJobResM (GF := GF) kb = iprop(True) := by
  unfold mvcc.compactJobResM; simp only [h, ↓reduceIte]

/-- Off, no reader is kept back for a job. -/
theorem mvcc.nJobRd_off (kb : Option mvcc.KBReal) (h : ¬ mvcc.kbCmpM kb) : mvcc.nJobRd kb = 0 := by
  unfold mvcc.nJobRd; unfold mvcc.kbCmpM at h
  cases kb with
  | none => rfl
  | some d => simp only at h ⊢; simp [h]

/-- Off, nothing deletable is today's. -/
theorem mvcc.kbNoDelOff_off (kb : Option mvcc.KBReal) (h : ¬ mvcc.kbCmpM kb) :
    mvcc.kbNoDelOff (GF := GF) kb = mvcc.kbNoDel kb := by
  unfold mvcc.kbNoDelOff; simp only [h, ↓reduceIte]

/-- A real backend that does not compact: its supply, slot and budgets are `True`, its job keeps no
reader. -/
theorem mvcc.cmOff_true (d : mvcc.KBReal) (hcm : d.cm = false) :
    ¬ mvcc.kbCmpM (some d) ∧ mvcc.nJobRd (some d) = 0 ∧
      mvcc.kbSRM (GF := GF) (some d) = iprop(True) ∧ mvcc.kbWTSupplyM (GF := GF) (some d) = iprop(True) ∧
      mvcc.compactJobResM (GF := GF) (some d) = iprop(True) := by
  have h : ¬ mvcc.kbCmpM (some d) := by simp [mvcc.kbCmpM, hcm]
  refine ⟨h, by simp [mvcc.nJobRd, hcm], ?_, ?_, ?_⟩
  · unfold mvcc.kbSRM; simp only [h, ↓reduceIte]
  · unfold mvcc.kbWTSupplyM; simp only [h, ↓reduceIte]
  · unfold mvcc.compactJobResM; simp only [h, ↓reduceIte]

/-- Off, the receipt is nothing. -/
theorem mvcc.restoreRcptM_off (d' : mvcc.KBReal) (L : mvcc.Log) (h : d'.cm = false) :
    mvcc.restoreRcptM (GF := GF) d' L = iprop(True) := by
  unfold mvcc.restoreRcptM; simp [h]

end vocab

end EtcdGrove
end Perennial
