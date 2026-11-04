/-
**Probe: the snapshot image of a compacting store** (2026-11-04, branch `mvcc-api`; not built by
any `lean_lib`, checked with `lake env lean`). Can the frozen API's `mvccImage D σ.log σ.crev u`
(`Spec/.../mvcc/Api.lean`, its docstring's obligations; `mvccImage_snapshot.law`) be produced from
what the store and the strengthened `backend.Snapshot` axiom (648d8e2bf4: `fkdOwn`, `fkVals D`)
give? Pure; no `sorry`, no `axiom`.

1. **The job's cut** (`entsCutAt_jobs`, `entsCutAt_jobStep`): the compaction job at `c₁`, deleting
   in revision order the entries with main `≤ c₁` not kept (`KeyDel`), leaves `entsCutAt L c` at
   every stopping point (any cursor `p : Rev`, so between two sub-revisions too), for every `c ≥ c₁`,
   after any earlier finished or partial jobs. Through `kiAvail_latest` (a kept revision is its
   key's latest at or below `c`: `keepAt_latest`, absent from the library), `KeyDel_down` (per key,
   deletability goes down the revisions) and `KeyDel_mono` (it grows with `c`: claimed by
   `entsCutAt`'s docstring, unproved until here). `entsCutAt` is the right snapshot-time fact but not
   inductive alone: the job's step also needs its loop invariant (every deletable entry below the
   cursor is gone, `hpast`); the inductive form is the closed form `entsOfJobs`.
2. **The image** (`image_of_obs`): from the job's cut, the records' agreement with the data
   (`fkVals D`) and the store's records' facts, `keyImageM true L r D` with `r.crev = c`, the mode
   off at `c = -1`, `u := r.resumes ↔` a scheduled record above the finished one, `c` the scheduled
   revision under `u`, and `L`'s last revision the largest of the bucket's last (as `restore()` reads
   it, `1` if empty) and the two records (`restoreCur_cut'`): derived, never exceeded.
3. **What the observation cannot give**:
   - the job's cut: the observation sees the physical `Key` bucket only thin of the logical view
     (`viewAt`'s `thinV`: present entries are the log's, missing ones deletable). That gives
     `entsCutAt`'s first two conjuncts (`obs_thin_cut12`) but not the third (per key, a prefix):
     `thin_not_cut` is a bucket with every observable fact and no `entsCutAt` (the bucket of
     `bucketThinnedAt_counterexample`, which rebuilds a wrong version).
   - the compaction at revision `0` (`crev0_corner`, `image_crev0_impossible`): the API allows
     `Compact(0)` (`KV.Compact.contract`, `MvccReachable.compact`); mid-job the data's records are
     `(none, some 0)`, whose restored revision is `-1`, so no `mvccImage D σ.log 0 u` of the
     docstring's form exists (`nonissues/etcd-restore-scheduled-compact-zero.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreImageOpen
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreCut
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchScan
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace snapProbe

section pure
variable [GooseExts]

/-! ## Revisions -/

theorem revLt_asymm {a b : Rev} (h1 : Rev.lt a b) (h2 : Rev.lt b a) : False := by
  unfold Rev.lt at h1 h2
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · omega
  · rw [e2] at h1; omega
  · rw [e1] at h2; omega
  · omega

theorem revLt_trans {a b d : Rev} (h1 : Rev.lt a b) (h2 : Rev.lt b d) : Rev.lt a d := by
  unfold Rev.lt at *
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · left; omega
  · left; rw [← e2]; exact h1
  · left; rw [e1]; exact h2
  · right; exact ⟨e1.trans e2, by omega⟩

/-! ## What compaction keeps (`kiAvail`) -/

/-- `kiAvail`, characterized: the `j`-th revision of `doCompact`'s generation, at or below `c`,
every later one of that generation above it. -/
theorem kiAvail_some {c : w64} {ki : KeyIndex} (hwf : KiWf ki) {r : Rev}
    (h : kiAvail c ki = some r) :
    ∃ (j : Nat) (hj : j < (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs.length),
      compactGenIdx c ki.gens < ki.gens.length ∧
      (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs[j] = r ∧
      sint.Z r.main ≤ sint.Z c ∧
      ∀ (k : Nat) (hk : k < (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs.length), j < k →
        sint.Z c < sint.Z ((ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs[k]).main := by
  have hlt := compactGenIdx_lt c ki.gens hwf.ne
  unfold kiAvail at h
  simp only [] at h
  generalize hg : ki.gens.getD (compactGenIdx c ki.gens) Gen.empty = g at *
  rcases genWalk_pAbove_spec g.revs c with ⟨hw, -⟩ | ⟨j, hj, hw, hjm, hjafter⟩
  · rw [hw] at h; simp at h
  · rw [hw] at h
    simp only [Int.toNat_natCast] at h
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at h
    simp only [Option.some.injEq] at h
    rw [getD_lt _ hj] at h
    exact ⟨j, hj, hlt, h, by rw [← h]; exact hjm, hjafter⟩

/-- **`keepAt_latest`: a kept revision is its key's latest at or below `c`**: every later
revision of the key index is above `c`. -/
theorem kiAvail_latest {c : w64} {ki : KeyIndex} (hs : KiS ki) {r r' : Rev}
    (ha : kiAvail c ki = some r) (hr' : r' ∈ kiRevs ki) (hlt : Rev.lt r r') :
    sint.Z c < sint.Z r'.main := by
  obtain ⟨j, hj, hgi, hrj, -, hafter⟩ := kiAvail_some hs.wf ha
  have hne : ki.gens ≠ [] := hs.wf.ne
  have hstop := compactGenIdx_stop c ki.gens hne
  generalize hgc : compactGenIdx c ki.gens = gi at *
  unfold kiRevs at hr'
  rw [List.mem_flatten] at hr'
  obtain ⟨rs, hrs, hr'm⟩ := hr'
  rw [List.mem_map] at hrs
  obtain ⟨g', hg', rfl⟩ := hrs
  obtain ⟨i', hi', hgi'⟩ := List.getElem_of_mem hg'
  have hg'd : ki.gens.getD i' Gen.empty = g' := by rw [getD_lt _ hi', hgi']
  have hrmem : r ∈ (ki.gens.getD gi Gen.empty).revs := by rw [← hrj]; exact List.getElem_mem hj
  have hr'mem : r' ∈ (ki.gens.getD i' Gen.empty).revs := by rw [hg'd]; exact hr'm
  rcases Nat.lt_trichotomy i' gi with hlt' | heq | hgt
  · exact (revLt_asymm hlt (hs.cross hlt' hgi hr'mem hrmem)).elim
  · subst heq
    obtain ⟨j', hj', hrj'⟩ := List.getElem_of_mem hr'mem
    rcases Nat.lt_trichotomy j' j with h1 | h1 | h1
    · have := List.pairwise_iff_getElem.1 (hs.gen_sorted hgi) j' j hj' hj h1
      rw [hrj', hrj] at this
      exact (revLt_asymm hlt this).elim
    · subst h1
      have : r = r' := hrj.symm.trans hrj'
      rw [this] at hlt
      exact (revLt_asymm hlt hlt).elim
    · have := hafter j' hj' h1
      rw [hrj'] at this
      exact this
  · -- a later generation: `doCompact` stopped at `gi`, which is not the last
    rcases hstop with hl | hadv
    · omega
    have hgne : (ki.gens.getD gi Gen.empty).revs ≠ [] := List.ne_nil_of_mem hrmem
    have htm := getLastD_mem _ Rev.zero hgne
    have htle := Rev.lt_main_le (hs.cross hgt hi' htm hr'mem)
    unfold genAdv at hadv
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hadv
    obtain ⟨hnlt, hn⟩ := hadv
    unfold tombZ at hnlt hn
    rcases hn with hne' | hrec
    · omega
    · -- the tombstone at `c`, the next generation not re-created at `c`
      have hn1 : gi + 1 < ki.gens.length := by omega
      obtain ⟨f, fs, hf⟩ : ∃ f fs, (ki.gens.getD (gi + 1) Gen.empty).revs = f :: fs := by
        rcases Nat.lt_or_eq_of_le (show gi + 1 ≤ i' by omega) with h | h
        · exact List.exists_cons_of_ne_nil (hs.wf.nonlast (gi + 1) (by omega))
        · rw [h]; exact List.exists_cons_of_ne_nil (List.ne_nil_of_mem hr'mem)
      have hfmem : f ∈ (ki.gens.getD (gi + 1) Gen.empty).revs := by
        rw [hf]; exact List.mem_cons_self
      have hlo := Rev.lt_main_le (hs.cross (Nat.lt_succ_self gi) hn1 htm hfmem)
      unfold genRecreatedAt at hrec
      rw [hf] at hrec
      simp only [decide_eq_false_iff_not] at hrec
      have hhi : sint.Z f.main ≤ sint.Z r'.main := by
        rcases Nat.lt_or_eq_of_le (show gi + 1 ≤ i' by omega) with h | h
        · exact Rev.lt_main_le (hs.cross h hi' hfmem hr'mem)
        · have hf' : (ki.gens.getD i' Gen.empty).revs = f :: fs := by rw [← h]; exact hf
          have hgs := hs.gen_sorted hi'
          rw [hf'] at hgs
          have hrm := hr'mem
          rw [hf'] at hrm
          rcases List.mem_cons.1 hrm with he | hm
          · rw [he]; exact Int.le_refl _
          · exact Rev.lt_main_le ((List.pairwise_cons.1 hgs).1 _ hm)
      omega

/-- **What compaction at `c` keeps, compaction at a lower `c₀` keeps** if it is at or below
`c₀`. -/
theorem kiAvail_down {c0 c : w64} {ki : KeyIndex} (hs : KiS ki) (hcc : sint.Z c0 ≤ sint.Z c)
    {r : Rev} (ha : kiAvail c ki = some r) (hr : sint.Z r.main ≤ sint.Z c0) :
    kiAvail c0 ki = some r := by
  obtain ⟨j, hj, hgi, hrj, -, hafter⟩ := kiAvail_some hs.wf ha
  have hne : ki.gens ≠ [] := hs.wf.ne
  have hstop := compactGenIdx_stop c ki.gens hne
  generalize hgc : compactGenIdx c ki.gens = gi at *
  have hrmem : r ∈ (ki.gens.getD gi Gen.empty).revs := by rw [← hrj]; exact List.getElem_mem hj
  have hidx : compactGenIdx c0 ki.gens = gi := by
    apply compactGenIdx_eq _ _ _ hgi
    · intro j' hj'
      have hne' : (ki.gens.getD j' Gen.empty).revs ≠ [] := hs.wf.nonlast j' (by omega)
      have htm := getLastD_mem _ Rev.zero hne'
      have hle := Rev.lt_main_le (hs.cross hj' hgi htm hrmem)
      rcases Int.lt_or_eq_of_le (Int.le_trans hle hr) with h1 | h1
      · apply genAdv_of_lt
        unfold tombZ
        exact h1
      have hn1 : j' + 1 < ki.gens.length := by omega
      obtain ⟨f, fs, hf⟩ : ∃ f fs, (ki.gens.getD (j' + 1) Gen.empty).revs = f :: fs := by
        rcases Nat.lt_or_eq_of_le (show j' + 1 ≤ gi by omega) with h | h
        · exact List.exists_cons_of_ne_nil (hs.wf.nonlast (j' + 1) (by omega))
        · rw [h]; exact List.exists_cons_of_ne_nil (List.ne_nil_of_mem hrmem)
      have hfmem : f ∈ (ki.gens.getD (j' + 1) Gen.empty).revs := by
        rw [hf]; exact List.mem_cons_self
      have hlo := Rev.lt_main_le (hs.cross (Nat.lt_succ_self j') hn1 htm hfmem)
      have hhi : sint.Z f.main ≤ sint.Z r.main := by
        rcases Nat.lt_or_eq_of_le (show j' + 1 ≤ gi by omega) with h | h
        · exact Rev.lt_main_le (hs.cross h hgi hfmem hrmem)
        · have hf' : (ki.gens.getD gi Gen.empty).revs = f :: fs := by rw [← h]; exact hf
          have hgs := hs.gen_sorted hgi
          rw [hf'] at hgs
          have hrm := hrmem
          rw [hf'] at hrm
          rcases List.mem_cons.1 hrm with he | hm
          · rw [he]; exact Int.le_refl _
          · exact Rev.lt_main_le ((List.pairwise_cons.1 hgs).1 _ hm)
      unfold genAdv
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      right
      refine ⟨by unfold tombZ; exact h1, ?_⟩
      unfold genRecreatedAt
      rw [hf]
      simp only [decide_eq_true_eq]
      omega
    · rcases hstop with h | h
      · exact Or.inl h
      · right
        cases hb : genAdv c0 (ki.gens.getD gi Gen.empty) (ki.gens.getD (gi + 1) Gen.empty)
        · rfl
        · rw [genAdv_mono hcc hb] at h; cases h
  unfold kiAvail
  simp only []
  rw [hidx]
  have hwc : genWalk (ki.gens.getD gi Gen.empty).revs (pAbove c0) = j := by
    apply genWalk_eq_some j hj
    · simp only [pAbove, decide_eq_false_iff_not, Int.not_lt]; rw [hrj]; exact hr
    · intro k hk hjk
      have := hafter k hk hjk
      simp only [pAbove, decide_eq_true_eq]; omega
  rw [hwc, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  simp only [Int.toNat_natCast]
  rw [getD_lt _ hj, hrj]

/-! ## The deletable entries (`KeyDel`) -/

/-- An entry of the bucket is an event's (same revision and key). -/
theorem ent_ev {L : Log} {e : KvEnt} (he : e ∈ logEnts L 0 L.length) :
    ∃ ev ∈ evsOf L, ev.rev = e.rev ∧ ev.key = e.kv.key := by
  obtain ⟨j, i, c, kv, -, -, hj, hgj, -, hc, hk, rfl⟩ := logEnts_entry L 0 L.length e he
  refine ⟨{ rev := ⟨W64 j, W64 i⟩, change := c }, mem_evsOf_of L j i _ c hgj hc, rfl, ?_⟩
  show c.key = kv.key
  unfold changeKv at hk
  rw [hc] at hk
  cases c with
  | put k v l => simp only at hk; exact (findKey_key hk).symm
  | del k => cases hk; rfl

/-- **Per key, deletability goes down the revisions**: an entry below a deletable entry of its
key is deletable (the later one is at or below `c` and not kept, so the earlier one is not the
key's latest at or below `c`, `kiAvail_latest`). -/
theorem KeyDel_down {L : Log} (hb : LogB L) (hwf : LogWf' L) {c : Int} {e₁ e₂ : KvEnt}
    (he₁ : e₁ ∈ logEnts L 0 L.length) (he₂ : e₂ ∈ logEnts L 0 L.length)
    (hk : e₁.kv.key = e₂.kv.key) (hlt : Rev.lt e₁.rev e₂.rev)
    (hd : KeyDel L c (revBytes e₂.rev e₂.tomb)) : KeyDel L c (revBytes e₁.rev e₁.tomb) := by
  obtain ⟨hcL, r, t, hrb, h0, h1, hnk⟩ := hd
  obtain ⟨-, rfl⟩ := revBytes_inj _ _ _ _ hrb
  have hbd := logEnts_bounds L hb.1 hb.2 0 L.length (Nat.le_refl _)
  have hm := Rev.lt_main_le hlt
  refine ⟨hcL, e₁.rev, e₁.tomb, rfl, (hbd e₁ he₁).1, by omega, ?_⟩
  rintro ⟨k, hka⟩
  obtain ⟨ev, hev, hevr, hevk⟩ := kiRevs_kiOfKey (kiAvail_mem hka)
  obtain ⟨ent, hent, hentr, hentk, -⟩ := logEnts_of_ev hev
  have hent1 : ent = e₁ := logEnts_rev_inj hb hent he₁ (hentr.trans hevr)
  subst hent1
  obtain ⟨ev₂, hev₂, hr₂, hk₂⟩ := ent_ev he₂
  have hmem := ev_mem_kiRevs L hwf hb.1 hb.2 ev₂ hev₂
  have hkk : ev₂.key = k := by rw [hk₂, ← hk, hentk, hevk]
  rw [hkk, hr₂] at hmem
  have hc0 : 0 ≤ c := by have := (hbd _ he₂).1; omega
  have hcz : sint.Z (W64 c) = c := sintZ_W64_of (by omega) (by have := hb.1; omega)
  have := kiAvail_latest (kiOfKey_KiS L hb k) hka hmem hlt
  omega

/-- **Deletability grows with the compaction revision** (`entsCutAt`'s docstring's "`KeyDel` grows
with `c`"). -/
theorem KeyDel_mono {L : Log} (hb : LogB L) {c0 c : Int} (h0 : -1 ≤ c0) (hcc : c0 ≤ c)
    (hc : c < L.length) {key : GoString} (hd : KeyDel L c0 key) : KeyDel L c key := by
  obtain ⟨-, r, t, rfl, hr0, hr1, hnk⟩ := hd
  have hl := hb.1
  have hz0 : sint.Z (W64 c0) = c0 := sintZ_W64_of h0 (by omega)
  have hz : sint.Z (W64 c) = c := sintZ_W64_of (by omega) (by omega)
  refine ⟨hc, r, t, rfl, hr0, by omega, ?_⟩
  rintro ⟨k, hk⟩
  exact hnk ⟨k, kiAvail_down (kiOfKey_KiS L hb k) (by omega) hk (by omega)⟩

/-- The job's shape at `c₀` is the job's shape at every later `c`. -/
theorem entsCutAt_mono {L : Log} (hb : LogB L) {c0 c : Int} (h0 : -1 ≤ c0) (hcc : c0 ≤ c)
    (hc : c < L.length) {ents : List KvEnt} (h : entsCutAt L c0 ents) : entsCutAt L c ents :=
  ⟨h.1, fun e he hn => KeyDel_mono hb h0 hcc hc (h.2.1 e he hn), h.2.2⟩

/-! ## 1. The job's cut at every stopping point -/

/-- The cursor `p` of a job (`none`: the job finished) is past the revision `r`. -/
def RevBelow (p : Option Rev) (r : Rev) : Prop := ∀ q, p = some q → Rev.lt r q

/-- **The entry `e` is gone** after the jobs `jobs`, each a compaction revision and its cursor (the
job at `c₁` has deleted, in revision order, the entries below its cursor that are deletable at
`c₁`): `kvstore_compaction.go`'s loop, whose batches may stop anywhere, between two sub-revisions
too. A finished job is `(c₀, none)`, a queued one `(c₂, some ⟨0, 0⟩)` (or absent). -/
def Gone (L : Log) (jobs : List (Int × Option Rev)) (e : KvEnt) : Prop :=
  ∃ j ∈ jobs, RevBelow j.2 e.rev ∧ KeyDel L j.1 (revBytes e.rev e.tomb)

open Classical in
/-- The bucket's entries after the jobs (the closed form of the job's state: the inductive
invariant). -/
def entsOfJobs (L : Log) (jobs : List (Int × Option Rev)) : List KvEnt :=
  (logEnts L 0 L.length).filter (fun e => decide (¬ Gone L jobs e))

open Classical in
theorem mem_entsOfJobs {L : Log} {jobs : List (Int × Option Rev)} {e : KvEnt} :
    e ∈ entsOfJobs L jobs ↔ e ∈ logEnts L 0 L.length ∧ ¬ Gone L jobs e := by
  unfold entsOfJobs
  rw [List.mem_filter, decide_eq_true_eq]

/-- **`entsCutAt_jobStep`, closed form: the jobs' bucket has the job's shape at every revision
at or above theirs**, at every stopping point of each (any cursor). -/
theorem entsCutAt_jobs {L : Log} (hb : LogB L) (hwf : LogWf' L) {c : Int} (hc : c < L.length)
    {jobs : List (Int × Option Rev)} (hjobs : ∀ j ∈ jobs, -1 ≤ j.1 ∧ j.1 ≤ c) :
    entsCutAt L c (entsOfJobs L jobs) := by
  refine ⟨List.filter_sublist, ?_, ?_⟩
  · intro e he hn
    have hg : Gone L jobs e := Classical.byContradiction fun h => hn (mem_entsOfJobs.2 ⟨he, h⟩)
    obtain ⟨j, hj, -, hd⟩ := hg
    exact KeyDel_mono hb (hjobs j hj).1 (hjobs j hj).2 hc hd
  · intro e₁ he₁ e₂ he₂ hk hlt hn₂
    have hg : Gone L jobs e₂ := Classical.byContradiction fun h => hn₂ (mem_entsOfJobs.2 ⟨he₂, h⟩)
    obtain ⟨j, hj, hbel, hd⟩ := hg
    intro hm₁
    apply (mem_entsOfJobs.1 hm₁).2
    exact ⟨j, hj, fun q hq => revLt_trans hlt (hbel q hq), KeyDel_down hb hwf he₁ he₂ hk hlt hd⟩

/-- **`entsCutAt_jobStep`: one deletion of the job at `c₁ ≤ c`** keeps the shape at `c`, given the
job's loop invariant (every entry below the deleted one deletable at `c₁` is gone, `hpast`), and
re-establishes that invariant one entry further. `entsCutAt` alone is not inductive: `hpast` is
the job's part. -/
theorem entsCutAt_jobStep {L : Log} (hb : LogB L) (hwf : LogWf' L) {c c₁ : Int} (h0 : -1 ≤ c₁)
    (hcc : c₁ ≤ c) (hc : c < L.length) {ents : List KvEnt} (hcut : entsCutAt L c ents)
    {e : KvEnt} (he : e ∈ logEnts L 0 L.length) (hdel : KeyDel L c₁ (revBytes e.rev e.tomb))
    (hpast : ∀ e' ∈ logEnts L 0 L.length, Rev.lt e'.rev e.rev →
      KeyDel L c₁ (revBytes e'.rev e'.tomb) → e' ∉ ents) :
    entsCutAt L c (ents.filter (fun x => decide (x.rev ≠ e.rev))) ∧
    ∀ e' ∈ logEnts L 0 L.length, (Rev.lt e'.rev e.rev ∨ e'.rev = e.rev) →
      KeyDel L c₁ (revBytes e'.rev e'.tomb) → e' ∉ ents.filter (fun x => decide (x.rev ≠ e.rev)) := by
  have hmem : ∀ x, x ∈ ents.filter (fun x => decide (x.rev ≠ e.rev)) ↔ x ∈ ents ∧ x.rev ≠ e.rev := by
    intro x; rw [List.mem_filter, decide_eq_true_eq]
  refine ⟨⟨List.filter_sublist.trans hcut.1, ?_, ?_⟩, ?_⟩
  · intro x hx hn
    by_cases hxe : x ∈ ents
    · have hr : x.rev = e.rev := Classical.byContradiction fun h => hn ((hmem x).2 ⟨hxe, h⟩)
      rw [logEnts_rev_inj hb hx he hr]
      exact KeyDel_mono hb h0 hcc hc hdel
    · exact hcut.2.1 x hx hxe
  · intro e₁ he₁ e₂ he₂ hk hlt hn₂ hm₁
    have hm₁' := ((hmem e₁).1 hm₁).1
    by_cases hx₂ : e₂ ∈ ents
    · have hr : e₂.rev = e.rev := Classical.byContradiction fun h => hn₂ ((hmem e₂).2 ⟨hx₂, h⟩)
      have h2e := logEnts_rev_inj hb he₂ he hr
      subst h2e
      exact hpast e₁ he₁ hlt (KeyDel_down hb hwf he₁ he₂ hk hlt hdel) hm₁'
    · exact hcut.2.2 e₁ he₁ e₂ he₂ hk hlt hx₂ hm₁'
  · intro e' he' hor hd hm'
    obtain ⟨hm', hne⟩ := (hmem e').1 hm'
    rcases hor with hlt | heq
    · exact hpast e' he' hlt hd hm'
    · exact hne heq

/-- The job skips a kept entry: its loop invariant extends past it. -/
theorem jobPast_skip {L : Log} (hb : LogB L) {c₁ : Int} {ents : List KvEnt} {e : KvEnt}
    (he : e ∈ logEnts L 0 L.length) (hkeep : ¬ KeyDel L c₁ (revBytes e.rev e.tomb))
    (hpast : ∀ e' ∈ logEnts L 0 L.length, Rev.lt e'.rev e.rev →
      KeyDel L c₁ (revBytes e'.rev e'.tomb) → e' ∉ ents) :
    ∀ e' ∈ logEnts L 0 L.length, (Rev.lt e'.rev e.rev ∨ e'.rev = e.rev) →
      KeyDel L c₁ (revBytes e'.rev e'.tomb) → e' ∉ ents := by
  intro e' he' hor hd
  rcases hor with hlt | heq
  · exact hpast e' he' hlt hd
  · rw [logEnts_rev_inj hb he' he heq] at hd; exact absurd hd hkeep

/-! ## 2. The image from the observation -/

/-- **The image, from the job's cut and the records** (the facts `mvccImage`'s docstring asks for):
the data's `Key` bucket is the jobs' (`hkey`: **not** from the observation, see `thin_not_cut`;
the store must track the jobs and the backend expose the physical bucket), its compaction keys hold
the store's records (`hfk`: the strengthened axiom's `fkVals D`, with mvcc's half of `fkdOwn`
agreeing with `metaCompact`), the records of the log, past `0` and restoring to the store's
compaction revision (`hrec`, `hpos`, `hrc`: the store's invariant; `hpos` needs `1 ≤ rev` at every
compaction, `crev0_corner`). Then: the mode on's image at `c`; at `c = -1` the mode off's
(`keyImage`); `u := rc.resumes` iff a scheduled record above the finished one, `c` the scheduled
revision then; and `L`'s last revision the largest of the bucket's last revision (`1` if empty, as
`restore()` reads it) and the two records. -/
theorem image_of_obs (R : Log) (hR : ∀ cs ∈ R, cs ≠ []) (hb : LogB ([[], []] ++ R))
    (hwf : LogWf' ([[], []] ++ R)) (c : Int) (rc : CmpRecs)
    (hrec : recsOk ([[], []] ++ R) rc) (hpos : recsPos rc) (hrc : rc.crev = c)
    (jobs : List (Int × Option Rev)) (hjobs : ∀ j ∈ jobs, -1 ≤ j.1 ∧ j.1 ≤ c)
    (D : backend.Data)
    (hkey : ∀ k, backend.dget D keyName k =
      (bucketOfEnts (entsOfJobs ([[], []] ++ R) jobs)).lookup k)
    (hfk : backend.fkVals D = (recBytes rc.fin, recBytes rc.sched)) :
    keyImageM true ([[], []] ++ R) rc D ∧ rc.crev = c ∧
      (c = -1 → keyImageM false ([[], []] ++ R) rc D) ∧
      (rc.resumes = true ↔ ∃ x, rc.sched = some x ∧ rc.finRev < sint.Z x) ∧
      (rc.resumes = true → c = rc.schedRev) ∧
      max (max (sint.Z (restoreLastRev (entsOfJobs ([[], []] ++ R) jobs))) rc.finRev)
        rc.schedRev = (([[], []] ++ R).length : Int) - 1 := by
  have hcL : c < (([[], []] ++ R).length : Int) := by
    rcases recsPos_crev rc hpos with h | h
    · rw [← hrc, h]; simp; omega
    · have hl : 2 ≤ ([[], []] ++ R).length := by simp
      have := recsOk_crev_lt _ rc hrec hl
      omega
  have hcut : entsCutAt ([[], []] ++ R) c (entsOfJobs ([[], []] ++ R) jobs) :=
    entsCutAt_jobs hb hwf hcL hjobs
  have hfin : backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName finKeyBytes =
      recBytes rc.fin := congrArg Prod.fst hfk
  have hsch : backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName schedKeyBytes =
      recBytes rc.sched := congrArg Prod.snd hfk
  have hon : keyImageM true ([[], []] ++ R) rc D := by
    unfold keyImageM
    simp only [↓reduceIte]
    exact ⟨_, hkey, hfin, hsch, hrec, hpos, hrc ▸ hcut⟩
  refine ⟨hon, hrc, fun h => keyImageM_off_of_on _ rc D hb hon (hrc.trans h), ?_, ?_, ?_⟩
  · have hs : ∀ x, rc.sched = some x → 1 ≤ sint.Z x := hpos.2
    unfold CmpRecs.resumes CmpRecs.schedRev
    cases h : rc.sched with
    | none => simp
    | some x =>
      have := hs x h
      simp only [Option.map_some, Option.getD_some, decide_eq_true_eq, Option.some.injEq,
        exists_eq_left']
      constructor
      · exact fun h' => h'.2
      · exact fun h' => ⟨by omega, h'⟩
  · intro h; rw [← hrc]; unfold CmpRecs.crev; rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  · exact restoreCur_cut' R hR hb rc hrec _ (hrc ▸ hcut)

/-! ### What the observation gives of the `Key` bucket, and what it does not -/

open Classical in
/-- The entries of a bucket `kb`: the log's whose bytes `kb` holds. -/
def entsIn (L : Log) (kb : Bucket) : List KvEnt :=
  (logEnts L 0 L.length).filter (fun e => decide ((kb.lookup (revBytes e.rev e.tomb)).isSome))

/-- **What the observation gives** (`viewAt`'s `thinV`, the store's `bucketLog`/`snapThin` and its
registered `delKey`, through `KeyDel_prefix` and `KeyDel_mono`, at the frozen state's log and
compaction revision): the physical bucket `kb` is a part of the log's (`hsub`) whose missing
entries are deletable at `c` (`hdel`). That makes `kb` the bucket of a sublist of the log's
entries with every missing entry deletable: `entsCutAt`'s first two conjuncts, not its third. -/
theorem obs_thin_cut12 (L : Log) (hb : LogB L) (c : Int) (kb : Bucket)
    (hsub : ∀ k v, kb.lookup k = some v → (bucketMap L).lookup k = some v)
    (hdel : ∀ k, (bucketMap L).lookup k ≠ none → kb.lookup k = none → KeyDel L c k) :
    (∀ k, kb.lookup k = (bucketOfEnts (entsIn L kb)).lookup k) ∧
      (entsIn L kb).Sublist (logEnts L 0 L.length) ∧
      (∀ e ∈ logEnts L 0 L.length, e ∉ entsIn L kb → KeyDel L c (revBytes e.rev e.tomb)) := by
  have hsl : (entsIn L kb).Sublist (logEnts L 0 L.length) := List.filter_sublist
  have hmemI : ∀ e, e ∈ entsIn L kb ↔ e ∈ logEnts L 0 L.length ∧
      (kb.lookup (revBytes e.rev e.tomb)).isSome = true := by
    intro e; unfold entsIn; rw [List.mem_filter, decide_eq_true_eq]
  have hfull := bucketOfEnts_lookup_iff L hb (List.Sublist.refl (logEnts L 0 L.length))
  have hpart := bucketOfEnts_lookup_iff L hb hsl
  rw [bucketOfEnts_logEnts] at hfull
  refine ⟨fun k => ?_, hsl, ?_⟩
  · cases hk : kb.lookup k with
    | none =>
      cases hb' : (bucketOfEnts (entsIn L kb)).lookup k with
      | none => rfl
      | some v =>
        have := (hpart k v).1 hb'
        obtain ⟨e, he, hpe⟩ := List.mem_map.1 this
        have hk' : revBytes e.rev e.tomb = k := congrArg Prod.fst hpe
        have := ((hmemI e).1 he).2
        rw [hk', hk] at this
        cases this
    | some v =>
      have h1 := (hfull k v).1 (hsub k v hk)
      obtain ⟨e, he, hpe⟩ := List.mem_map.1 h1
      have hk' : revBytes e.rev e.tomb = k := congrArg Prod.fst hpe
      have hin : e ∈ entsIn L kb := (hmemI e).2 ⟨he, by rw [hk', hk]; rfl⟩
      exact ((hpart k v).2 (List.mem_map.2 ⟨e, hin, hpe⟩)).symm
  · intro e he hn
    have hnone : kb.lookup (revBytes e.rev e.tomb) = none := by
      cases h : kb.lookup (revBytes e.rev e.tomb) with
      | none => rfl
      | some v => exact absurd ((hmemI e).2 ⟨he, by rw [h]; rfl⟩) hn
    apply hdel _ _ hnone
    rw [(hfull _ (kvEncode e.kv)).2 (List.mem_map.2 ⟨e, he, rfl⟩)]
    simp

/-- **The observation does not give the job's cut**: the bucket of `cx2Log` (three puts of one key,
at `2`, `3`, `4`) without revision `3` satisfies everything the observation gives at `c = 4` (a
sublist of the log's entries, every missing one deletable: `obs_thin_cut12`'s conclusion) and is
not of the job's shape (`entsCutAt`'s third conjunct: `3` gone, `2` kept). It rebuilds the wrong
version (`bucketThinnedAt_counterexample`). The job never leaves it; only mvcc knows that, and the
backend's observation has no way to tell it apart. -/
theorem thin_not_cut :
    let ents := [cx2Ent (W64 2) (W64 1) [W8 120], cx2Ent (W64 4) (W64 3) [W8 122]]
    ents.Sublist (logEnts cx2Log 0 cx2Log.length) ∧
      (∀ e ∈ logEnts cx2Log 0 cx2Log.length, e ∉ ents → KeyDel cx2Log 4 (revBytes e.rev e.tomb)) ∧
      ¬ entsCutAt cx2Log 4 ents := by
  intro ents
  refine ⟨?_, bucketThinnedAt_counterexample.1, ?_⟩
  · rw [cx2_logEnts]
    exact .cons_cons _ (.cons _ (.cons_cons _ .slnil))
  · intro h
    have h3 := h.2.2 (cx2Ent (W64 2) (W64 1) [W8 120]) (by rw [cx2_logEnts]; simp)
      (cx2Ent (W64 3) (W64 2) [W8 121]) (by rw [cx2_logEnts]; simp) rfl (Or.inl (by decide))
      (by simp [ents])
    exact h3 (by simp [ents])

/-! ### The compaction at revision `0` -/

/-- **The corner the docstring's obligations miss**: `Compact(0)` is a step of the API
(`MvccReachable.compact`, `KV.Compact.contract`: `σ.crev = -1 < 0 ≤ σ.rev`). Until its job
finishes, the data's records are `(none, some 0)` (`updateCompactRev` force-commits the scheduled
one), which `restore()` restores to `-1` (a scheduled `0` is never resumed) and which are not past
`0` (`recsPos`). -/
theorem crev0_corner :
    api.MvccReachable (api.mvccStart.compactTo 0) ∧ (api.mvccStart.compactTo 0).crev = 0 ∧
      (⟨none, some (W64 0)⟩ : CmpRecs).crev = -1 ∧
      (⟨none, some (W64 0)⟩ : CmpRecs).resumes = false ∧
      ¬ recsPos ⟨none, some (W64 0)⟩ := by
  refine ⟨api.MvccReachable.compact _ 0 api.MvccReachable.start rfl (by decide) (by decide), rfl,
    by decide, by decide, ?_⟩
  rintro ⟨-, h⟩
  have := h (W64 0) rfl
  revert this; decide

/-- **No restore image at `0` over such data**: with the data's records `(none, some 0)`, no
`keyImageM true L r D` has `r.crev = 0` (it would need `recsPos r`, and the records are the
data's). So `mvccImage D σ.log 0 u`, the restore image at `c ≠ -1`, cannot be produced mid-job of
`Compact(0)`: `mvccImage_snapshot.law` needs the scope restriction `1 ≤ rev` (as
`EtcdServer.Compact.spec` already has) or a weaker post. -/
theorem image_crev0_impossible (L : Log) (r : CmpRecs) (D : backend.Data)
    (hs : backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName schedKeyBytes =
      recBytes (some (W64 0))) :
    ¬ keyImageM true L r D := by
  intro h
  unfold keyImageM at h
  simp only [↓reduceIte] at h
  obtain ⟨ents, -, -, hsched, -, hpos, -⟩ := h
  rw [hs] at hsched
  cases hr : r.sched with
  | none => rw [hr] at hsched; simp [recBytes] at hsched
  | some x =>
    rw [hr] at hsched
    simp only [recBytes, Option.map_some, Option.some.injEq] at hsched
    obtain ⟨-, hx⟩ := revBytes_inj _ _ _ _ hsched
    simp only [Rev.mk.injEq] at hx
    have := hpos.2 x hr
    rw [← hx.1] at this
    revert this; decide

/-! ### The log's shape (for `image_of_obs`'s `R`) -/

/-- A reachable state's log is the two empty revisions followed by non-empty ones. -/
theorem reach_shape (σ : api.MvccState) (h : api.MvccReachable σ) :
    ∃ R : Log, σ.log = [[], []] ++ R ∧ ∀ cs ∈ R, cs ≠ [] := by
  induction h with
  | start => exact ⟨[], rfl, by simp⟩
  | notify σ pend _ _ _ ih => exact ih
  | commit σ _ ih =>
    obtain ⟨R, hR, hne⟩ := ih
    show ∃ R', commitLog σ.log (σ.pending.getD []) = _ ∧ _
    unfold commitLog
    split
    · exact ⟨R, hR, hne⟩
    · rename_i hp
      refine ⟨R ++ [σ.pending.getD []], by rw [hR, List.append_assoc], ?_⟩
      intro cs hcs
      rcases List.mem_append.1 hcs with h | h
      · exact hne cs h
      · rw [List.mem_singleton.1 h]; exact hp
  | compact σ r _ _ _ _ ih => exact ih

end pure

#print axioms entsCutAt_jobs
#print axioms entsCutAt_jobStep
#print axioms image_of_obs
#print axioms obs_thin_cut12
#print axioms thin_not_cut
#print axioms crev0_corner
#print axioms image_crev0_impossible

end snapProbe
end mvcc
end EtcdGrove
end Perennial
