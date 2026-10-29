/-
**A database image's key view** (D22 S-f, 2026-10-19; `notes/decisions.md`, "D22 S-f carried
out"): what a received backend image says to the mvcc store that restores from it (D22 S-g).
Lean-first (no Rocq counterpart).

`keyImage log D`: bbolt's data `D` holds, in the `Key` bucket, the bucket of the log `log`
(`bucketMap`: an entry per change of every revision), and, in the `Meta` bucket, neither of the
compaction's keys (`scheduledCompactRev`, `finishedCompactRev`): the image of a store that never
compacted, which is the server's KV model's (its workload has no compaction: `apply.dispatchOk`).
D19l (v) (A) would replace "neither key" by the keys a model of the compactions gives
(`notes/snapshot-path-s0.md`, part 2, exception 2: the key bucket's physical content then
depends on the compaction job's progress, its logical view does not). The image's other buckets
are the server's (`etcdserver/InvImage.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CommitLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI backend

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`D`'s key view is the log `log`'s, with no compaction recorded** (see the file header). -/
def keyImage (log : Log) (D : Data) : Prop :=
  (∀ k, dget D keyName k = (bucketMap log).lookup k) ∧
  dget D go_etcd_io.etcd.server.v3.storage.schema.metaName schedKeyBytes = none ∧
  dget D go_etcd_io.etcd.server.v3.storage.schema.metaName finKeyBytes = none

/-- **`D` records no compaction**: its `Meta` bucket holds neither compaction key (a backend
opened over `D` gives its no-compaction token `bkNoCmp`: `bkNoCmp_of_fkCl`; D22 S-g). -/
def noCmpData (D : Data) : Prop :=
  dget D go_etcd_io.etcd.server.v3.storage.schema.metaName schedKeyBytes = none ∧
  dget D go_etcd_io.etcd.server.v3.storage.schema.metaName finKeyBytes = none

/-- Data with no compaction recorded has none of the keys the backend tracks (`fkKey`: the same
two keys of `Meta`). -/
theorem fkAbsD_of_noCmp {D : Data} (h : noCmpData D) : fkAbsD D := by
  intro n k hk
  obtain ⟨rfl, hk⟩ := hk
  rcases hk with rfl | rfl
  · exact h.1
  · exact h.2

omit package_sem in
/-- **The no-compaction token of a backend opened over data with no compaction recorded**
(the backend-compaction stage, 2026-10-29): the creator's half of the backend's compaction-key flag
(`newPostK`'s `fkCl γ P D`) is at `0`. -/
theorem bkNoCmp_of_fkCl (γ : BNames) (P : BParams) {D : Data} (h : noCmpData D) :
    fkCl (GF := GF) γ P D ⊢ bkNoCmp γ := by
  unfold fkCl
  rw [fkInit_of_abs (fkAbsD_of_noCmp h)]
  unfold bkNoCmp
  iintro ⟨H, -⟩; iexact H

omit package_sem in
/-- The same data's compaction keys are well formed: the bit at `true` (question 4, 2026-10-29). -/
theorem fkV_of_fkCl (γ : BNames) (P : BParams) {D : Data} (h : noCmpData D) :
    fkCl (GF := GF) γ P D ⊢ fkV γ true := by
  unfold fkCl
  have hw : fkWInit P D = true := by
    unfold fkWInit; simpa using fkWfD_of_abs P (fkAbsD_of_noCmp h)
  rw [hw]
  iintro ⟨-, H⟩; iexact H

omit package_sem in
/-- **Both from one creation resource** (review round 10, R10-1: the wiring needs the token and the
bit from the same `fkCl`): over data with no compaction recorded, the no-compaction token and the
bit at `true`. -/
theorem bkNoCmp_fkV_of_fkCl (γ : BNames) (P : BParams) {D : Data} (h : noCmpData D) :
    fkCl (GF := GF) γ P D ⊢ bkNoCmp γ ∗ fkV γ true := by
  unfold fkCl
  have hw : fkWInit P D = true := by
    unfold fkWInit; simpa using fkWfD_of_abs P (fkAbsD_of_noCmp h)
  rw [fkInit_of_abs (fkAbsD_of_noCmp h), hw]
  unfold bkNoCmp
  iintro ⟨H, Hv⟩
  iframe H Hv

omit package_sem in
/-- **The bit over data whose compaction keys are well formed** (R10-1; a restart over a file that
records a compaction): the client's half of the flag at `fkInit D` and the bit at `true`. -/
theorem fkCl_wf (γ : BNames) (P : BParams) {D : Data} (h : fkWfD P D) :
    fkCl (GF := GF) γ P D ⊢ fkOwn γ (fkInit D) ∗ fkV γ true := by
  unfold fkCl
  have hw : fkWInit P D = true := by
    unfold fkWInit; simpa using h
  rw [hw]

/-- A key image records no compaction. -/
theorem keyImage_noCmp {log : Log} {D : Data} (h : keyImage log D) : noCmpData D := h.2

/-- The readers' view of a backend opened over a key image, under the bridge's parameters, is
its log's bucket (what `newPost`'s `bView` and the store's `restore` read). -/
theorem keyView_of_dget {P : BParams} (hP : bridgeParams P) {m : Bucket} {D : Data}
    (h : ∀ k, dget D keyName k = m.lookup k) : keyView (vData P (D, ⟨∅, W64 0⟩)) m := by
  intro n k
  rw [vData_lookup]
  obtain ⟨-, -, hHB, -⟩ := hP
  rw [hHB n]
  by_cases hn : n = keyName
  · subst hn
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [vOf_emptyR]
    exact h k
  · have hn' : n ≠ go_etcd_io.etcd.server.v3.storage.schema.keyName := hn
    simp only [hn', ne_eq, not_false_eq_true, decide_true, ↓reduceIte]

/-- The readers' view of a key image (`keyView_of_dget`). -/
theorem keyView_of_keyImage {P : BParams} (hP : bridgeParams P) {log : Log} {D : Data}
    (h : keyImage log D) : keyView (vData P (D, ⟨∅, W64 0⟩)) (bucketMap log) :=
  keyView_of_dget hP h.1

/-- Conversely, a backend data whose readers' view is a bucket `m` holds `m` in its `Key`
bucket (what the snapshot's observation, `backend.Snapshot.spec`, gives of `sData P D`). -/
theorem dget_of_keyView {P : BParams} (hP : bridgeParams P) {m : Bucket} {D : Data}
    (h : keyView (sData P D) m) (k : GoString) : dget D keyName k = m.lookup k := by
  have := h keyName k
  unfold sData at this
  rw [vData_lookup] at this
  obtain ⟨-, -, hHB, -⟩ := hP
  rw [hHB keyName] at this
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
    vOf_emptyR] at this
  exact this

end lemmas

end mvcc
end EtcdGrove
end Perennial
