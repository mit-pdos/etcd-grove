/-
**The sender's snapshot image: the pure core** (stage 2, M2, 2026-11-05; moved from probe 2,
`notes/mvcc-api-probes/SnapImageProbe.lean`, whose counterexamples stay there). Lean-first (no Rocq
counterpart).

* **The job's cut** (`entsCutAt_jobs`, `entsCutAt_jobStep`, `jobPast_skip`): the compaction jobs,
  each deleting in revision order the entries with main at most its revision that it does not keep
  (`KeyDel`), leave `entsCutAt L c` at every stopping point, for every `c` at or above theirs
  (`KeyDel_down`, `KeyDel_mono`, `kiAvail_latest`).
* **The image's facts** (`imageOk`): what `mvccImage D L c u` holds besides its receipt: the `Key`
  bucket the entries `ents` cut at `c`, the `Meta` bucket's compaction keys the records `rc`, of `L`
  and past `0`, restoring to `c` (`rc.crev = c`), resumed iff `u`, and `L`'s last revision the
  largest of the bucket's and the records' (`restore()`'s `currentRev`); the log well formed, of a
  reachable state's shape. `imageOk_keyImageM`: the restore image `keyImageM` (both modes at `-1`);
  `imageOk_fresh`: a fresh backend's.
* **The image from a snapshot's observation** (`key_of_cut`, `imageOk_of_cut`): the physical `Key`
  bucket is the logical one (`m`, the store's view) but the deleted entries `X` (`dlVd`), so the
  store's cut fact on `(m, X)` (`cutOk`) is the data's; with the compaction keys' values the
  records', the image.
* **The cut under the store's steps**: a raised compaction revision (`cutOk_mono`), the job's
  delete (`cutAt_del`), a commit's new revision (`cutOk_append`, with the running job's loop
  invariant `jobPast`, `jobPast_append`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreImageOpen
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreCut
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchScan
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClientLaws
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace snap

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

/-! ### The acceptance check: the strengthened observation gives the job's cut (2026-11-04)

The user (2026-11-04): "the snapshot axiom should imply that the snapshot when restored from will
give a correct view of the abstract etcd state associated with that snapshot". The `Snapshot`
axiom now hands the observation, with the quarter of the readers' view at the logical view `Lv`
(the physical view `vd` thin of it), the batch lock's half of the safe-range buckets' deleted
entries `X` and `vd` exactly `Lv` but `X` there (`viewAtD`'s `dlVd`). With the store's facts -- its
logical bucket is its log's (`hLv`: mvcc's `bucketView`, agreeing with the clients' view) and the
deleted entries are what its compaction jobs deleted (`hX`: the client's half of `X`, kept by the
store's compaction beside the jobs' cursors) -- the data's `Key` bucket is the jobs' (`key_of_obs_exact`,
derived, not assumed), and so the image (`image_of_obs_exact`). -/

/-- **The data's `Key` bucket is the jobs'**, from the strengthened observation. -/
theorem key_of_obs_exact (L : Log) (hb : LogB L) (jobs : List (Int × Option Rev))
    (P : backend.BParams) (hsb : P.SB keyName = true) (hhb : P.HB keyName = false)
    (vd Lv X : backend.VData) (D : backend.Data)
    (hvd : ∀ k, vd.lookup (keyName, k) = backend.dget D keyName k)
    (hLv : ∀ k, Lv.lookup (keyName, k) = (bucketMap L).lookup k)
    (hsub : ∀ nk v, vd.lookup nk = some v → Lv.lookup nk = some v)
    (hdl : backend.dlVd P vd Lv X)
    (hX : ∀ k, X.lookup (keyName, k) ≠ none ↔
      ∃ e ∈ logEnts L 0 L.length, revBytes e.rev e.tomb = k ∧ Gone L jobs e) :
    ∀ k, backend.dget D keyName k = (bucketOfEnts (entsOfJobs L jobs)).lookup k := by
  have hsl : (entsOfJobs L jobs).Sublist (logEnts L 0 L.length) := List.filter_sublist
  have hpart := bucketOfEnts_lookup_iff L hb hsl
  have hfull := bucketOfEnts_lookup_iff L hb (List.Sublist.refl (logEnts L 0 L.length))
  rw [bucketOfEnts_logEnts] at hfull
  -- two of the log's entries with the same bytes are one
  have huniq : ∀ e₁ ∈ logEnts L 0 L.length, ∀ e₂ ∈ logEnts L 0 L.length,
      revBytes e₁.rev e₁.tomb = revBytes e₂.rev e₂.tomb → e₁ = e₂ := by
    intro e₁ h₁ e₂ h₂ h
    exact logEnts_rev_inj hb h₁ h₂ (revBytes_inj _ _ _ _ h).2
  intro k
  rw [← hvd]
  cases hm : (bucketMap L).lookup k with
  | none =>
    have hv : vd.lookup (keyName, k) = none := by
      cases h : vd.lookup (keyName, k) with
      | none => rfl
      | some w => have := hsub _ w h; rw [hLv, hm] at this; cases this
    rw [hv]; symm
    cases h2 : (bucketOfEnts (entsOfJobs L jobs)).lookup k with
    | none => rfl
    | some v =>
      obtain ⟨e, he, hpe⟩ := List.mem_map.1 ((hpart k v).1 h2)
      have := (hfull k v).2 (List.mem_map.2 ⟨e, hsl.subset he, hpe⟩)
      rw [hm] at this; cases this
  | some v =>
    cases hx : X.lookup (keyName, k) with
    | some x =>
      have hxn : X.lookup (keyName, k) ≠ none := by rw [hx]; simp
      have hv := (hdl.2 _ hxn).2.2.1
      rw [hv]; symm
      obtain ⟨e, he, hek, hg⟩ := (hX k).1 hxn
      cases h2 : (bucketOfEnts (entsOfJobs L jobs)).lookup k with
      | none => rfl
      | some v' =>
        obtain ⟨e', he', hpe'⟩ := List.mem_map.1 ((hpart k v').1 h2)
        have hk' : revBytes e'.rev e'.tomb = k := congrArg Prod.fst hpe'
        have := huniq e' (hsl.subset he') e he (hk'.trans hek.symm)
        subst this
        exact absurd hg (mem_entsOfJobs.1 he').2
    | none =>
      have hLn : Lv.lookup (keyName, k) ≠ none := by rw [hLv, hm]; simp
      have hvn : vd.lookup (keyName, k) ≠ none := by
        intro h
        exact (hdl.1 _ hsb hhb hLn h) hx
      cases hw : vd.lookup (keyName, k) with
      | none => exact absurd hw hvn
      | some w =>
        have hw' := hsub _ w hw
        rw [hLv, hm] at hw'
        cases hw'
        symm
        obtain ⟨e, he, hpe⟩ := List.mem_map.1 ((hfull k v).1 hm)
        have hk' : revBytes e.rev e.tomb = k := congrArg Prod.fst hpe
        have hng : ¬ Gone L jobs e := by
          intro hg
          exact ((hX k).2 ⟨e, he, hk', hg⟩) hx
        exact (hpart k v).2 (List.mem_map.2 ⟨e, mem_entsOfJobs.2 ⟨he, hng⟩, hpe⟩)

/-- **The acceptance check** (the user's criterion, 2026-11-04): from the strengthened
observation's facts (the logical view `Lv`, the exact deleted entries `X`, the compaction keys'
values `fkVals D`) and the store's (its log `[[], []] ++ R` and compaction revision `c`, its
records, its jobs and that `X` is what they deleted), the snapshot's data is the image `restore()`
reads: `image_of_obs`'s conclusion, its `Key` bucket premise derived (`key_of_obs_exact`). -/
theorem image_of_obs_exact (R : Log) (hR : ∀ cs ∈ R, cs ≠ []) (hb : LogB ([[], []] ++ R))
    (hwf : LogWf' ([[], []] ++ R)) (c : Int) (rc : CmpRecs)
    (hrec : recsOk ([[], []] ++ R) rc) (hpos : recsPos rc) (hrc : rc.crev = c)
    (jobs : List (Int × Option Rev)) (hjobs : ∀ j ∈ jobs, -1 ≤ j.1 ∧ j.1 ≤ c)
    (P : backend.BParams) (hsb : P.SB keyName = true) (hhb : P.HB keyName = false)
    (vd Lv X : backend.VData) (D : backend.Data)
    (hvd : ∀ k, vd.lookup (keyName, k) = backend.dget D keyName k)
    (hLv : ∀ k, Lv.lookup (keyName, k) = (bucketMap ([[], []] ++ R)).lookup k)
    (hsub : ∀ nk v, vd.lookup nk = some v → Lv.lookup nk = some v)
    (hdl : backend.dlVd P vd Lv X)
    (hX : ∀ k, X.lookup (keyName, k) ≠ none ↔
      ∃ e ∈ logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length,
        revBytes e.rev e.tomb = k ∧ Gone ([[], []] ++ R) jobs e)
    (hfk : backend.fkVals D = (recBytes rc.fin, recBytes rc.sched)) :
    keyImageM true ([[], []] ++ R) rc D ∧ rc.crev = c ∧
      (c = -1 → keyImageM false ([[], []] ++ R) rc D) ∧
      (rc.resumes = true ↔ ∃ x, rc.sched = some x ∧ rc.finRev < sint.Z x) ∧
      (rc.resumes = true → c = rc.schedRev) ∧
      max (max (sint.Z (restoreLastRev (entsOfJobs ([[], []] ++ R) jobs))) rc.finRev)
        rc.schedRev = (([[], []] ++ R).length : Int) - 1 :=
  image_of_obs R hR hb hwf c rc hrec hpos hrc jobs hjobs D
    (key_of_obs_exact _ hb jobs P hsb hhb vd Lv X D hvd hLv hsub hdl hX) hfk

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
  | compact σ r _ _ _ _ _ ih => exact ih


/-! ## The image's facts -/

/-- **The image's facts** (`mvccImage`'s pure part; `notes/mvcc-api-invariants.md` §2): the `Key`
bucket of `D` the entries `ents` cut at `c` (the job's shape, `entsCutAt`), the compaction keys the
records `rc`, of `L` and past revision `0`, restoring to `c` and resumed iff `u`, `L`'s last
revision the largest of the bucket's last (`1` if empty) and the records' (`restoreCur_cut'`), and
`L` well formed, of a reachable state's shape (two empty revisions, then non-empty ones). -/
def imageOk (D : backend.Data) (L : Log) (c : Int) (u : Bool) : Prop :=
  ∃ (rc : CmpRecs) (ents : List KvEnt),
    (∀ k, backend.dget D keyName k = (bucketOfEnts ents).lookup k) ∧
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName finKeyBytes = recBytes rc.fin ∧
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName schedKeyBytes =
      recBytes rc.sched ∧
    recsOk L rc ∧ recsPos rc ∧ entsCutAt L c ents ∧ rc.crev = c ∧ rc.resumes = u ∧
    max (max (sint.Z (restoreLastRev ents)) rc.finRev) rc.schedRev = (L.length : Int) - 1 ∧
    LogB L ∧ LogWf' L ∧ ∃ R : Log, L = [[], []] ++ R ∧ ∀ cs ∈ R, cs ≠ []

/-- **The image is the restore image** (`keyImageM`, mode on; off too at `c = -1`). -/
theorem imageOk_keyImageM {D : backend.Data} {L : Log} {c : Int} {u : Bool} (h : imageOk D L c u) :
    ∃ rc : CmpRecs, keyImageM true L rc D ∧ rc.crev = c ∧ rc.resumes = u ∧
      (c = -1 → keyImageM false L rc D) := by
  obtain ⟨rc, ents, hk, hfin, hsch, hrec, hpos, hcut, hrc, hu, -, hb, -, -⟩ := h
  have hon : keyImageM true L rc D := by
    unfold keyImageM
    simp only [↓reduceIte]
    exact ⟨ents, hk, hfin, hsch, hrec, hpos, hrc ▸ hcut⟩
  exact ⟨rc, hon, hrc, hu, fun h1 => keyImageM_off_of_on L rc D hb hon (hrc.trans h1)⟩

theorem logEnts_init : logEnts ([[], []] : Log) 0 2 = [] := by decide

/-- **A fresh backend's image**: no key, no compaction record, at the empty history. -/
theorem imageOk_fresh (D : backend.Data) (hk : ∀ k, backend.dget D keyName k = none)
    (hs : backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName schedKeyBytes = none)
    (hf : backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName finKeyBytes = none) :
    imageOk D api.mvccStart.log api.mvccStart.crev false := by
  have hwf := (api.reach_logWf api.mvccStart api.MvccReachable.start).1
  have hrec : recsOk api.mvccStart.log CmpRecs.empty := by
    unfold recsOk; simp [CmpRecs.empty]
  have hpos : recsPos CmpRecs.empty := by unfold recsPos; simp [CmpRecs.empty]
  have hb : LogB api.mvccStart.log := ⟨by decide, by decide⟩
  refine ⟨CmpRecs.empty, [], fun k => ?_, hf, hs, hrec, hpos, ?_, CmpRecs.crev_empty,
    CmpRecs.resumes_empty, ?_, hb, hwf, [], rfl, by simp⟩
  · rw [hk]; rfl
  · show entsCutAt [[], []] (-1) []
    refine ⟨?_, ?_, ?_⟩
    · show List.Sublist [] (logEnts [[], []] 0 2); exact List.nil_sublist _
    · intro e he; rw [show ([[], []] : Log).length = 2 from rfl, logEnts_init] at he; cases he
    · intro e₁ he₁; rw [show ([[], []] : Log).length = 2 from rfl, logEnts_init] at he₁; cases he₁
  · show max (max (sint.Z (restoreLastRev ([] : List KvEnt))) CmpRecs.empty.finRev)
      CmpRecs.empty.schedRev = (([[], []] : Log).length : Int) - 1
    rw [CmpRecs.finRev_empty]
    have h1 : sint.Z (restoreLastRev ([] : List KvEnt)) = 1 := rfl
    have h2 : CmpRecs.empty.schedRev = 0 := rfl
    rw [h1, h2]; decide

/-! ## The image from a snapshot's observation -/

/-- **The data's `Key` bucket from the observation and the store's cut** (`key_of_obs_exact`,
generalized: the logical view is the store's `m`, of any shape): the physical view `vd` is the
logical view `Lv` (`m` on the `Key` bucket) but the deleted entries `X` (`dlVd`), so the data's
bucket is the cut's. -/
theorem key_of_cut (P : backend.BParams) (hsb : P.SB keyName = true) (hhb : P.HB keyName = false)
    (vd Lv X : backend.VData) (D : backend.Data) (m : Bucket) (ents : List KvEnt)
    (hvd : ∀ k, vd.lookup (keyName, k) = backend.dget D keyName k)
    (hLv : ∀ k, Lv.lookup (keyName, k) = m.lookup k)
    (hsub : ∀ nk v, vd.lookup nk = some v → Lv.lookup nk = some v)
    (hdl : backend.dlVd P vd Lv X)
    (hcut : ∀ k, (if (X.lookup (keyName, k)).isSome then none else m.lookup k) =
      (bucketOfEnts ents).lookup k) :
    ∀ k, backend.dget D keyName k = (bucketOfEnts ents).lookup k := by
  intro k
  rw [← hvd, ← hcut k]
  cases hx : X.lookup (keyName, k) with
  | some x =>
    have hxn : X.lookup (keyName, k) ≠ none := by rw [hx]; simp
    simp only [Option.isSome_some, ↓reduceIte]
    exact (hdl.2 _ hxn).2.2.1
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    cases hm : m.lookup k with
    | none =>
      cases hw : vd.lookup (keyName, k) with
      | none => rfl
      | some w => have := hsub _ w hw; rw [hLv, hm] at this; cases this
    | some v =>
      have hLn : Lv.lookup (keyName, k) ≠ none := by rw [hLv, hm]; simp
      cases hw : vd.lookup (keyName, k) with
      | none => exact absurd hx (hdl.1 _ hsb hhb hLn hw)
      | some w =>
        have := hsub _ w hw
        rw [hLv, hm] at this
        exact this.symm ▸ rfl

/-- **The image from the observation and the store's facts**: the store's log `L` (a reachable
state's shape, certified), its records `rc` of `L` past `0` restoring to `c`, its cut on its view
and the deleted entries, the observation's view (`dlVd`, thin of the logical view `m`) and the
compaction keys' values the records'. -/
theorem imageOk_of_cut (R : Log) (hR : ∀ cs ∈ R, cs ≠ []) (hb : LogB ([[], []] ++ R))
    (hwf : LogWf' ([[], []] ++ R)) (c : Int) (rc : CmpRecs)
    (hrec : recsOk ([[], []] ++ R) rc) (hpos : recsPos rc) (hrc : rc.crev = c)
    (P : backend.BParams) (hsb : P.SB keyName = true) (hhb : P.HB keyName = false)
    (vd Lv X : backend.VData) (D : backend.Data) (m : Bucket)
    (hvd : ∀ k, vd.lookup (keyName, k) = backend.dget D keyName k)
    (hLv : ∀ k, Lv.lookup (keyName, k) = m.lookup k)
    (hsub : ∀ nk v, vd.lookup nk = some v → Lv.lookup nk = some v)
    (hdl : backend.dlVd P vd Lv X) (hcut : cutOk ([[], []] ++ R) m X c)
    (hfk : backend.fkVals D = (recBytes rc.fin, recBytes rc.sched)) :
    imageOk D ([[], []] ++ R) c rc.resumes := by
  obtain ⟨ents, hcutE, hcutB⟩ := hcut
  have hkey := key_of_cut P hsb hhb vd Lv X D m ents hvd hLv hsub hdl hcutB
  have hfin : backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName finKeyBytes =
      recBytes rc.fin := congrArg Prod.fst hfk
  have hsch : backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName schedKeyBytes =
      recBytes rc.sched := congrArg Prod.snd hfk
  exact ⟨rc, ents, hkey, hfin, hsch, hrec, hpos, hcutE, hrc, rfl,
    restoreCur_cut' R hR hb rc hrec ents (hrc ▸ hcutE), hb, hwf, R, rfl, hR⟩

/-! ## The store's cut under its steps (for the store-side tracking, `snapObs_M1`'s replacement) -/

/-- **A raised compaction revision keeps the cut** (`Compact`'s scheduled record, a later job). -/
theorem cutOk_mono {L : Log} (hb : LogB L) {m : Bucket} {X : backend.VData} {c0 c : Int}
    (h0 : -1 ≤ c0) (hcc : c0 ≤ c) (hc : c < L.length) (h : cutOk L m X c0) : cutOk L m X c := by
  obtain ⟨ents, hcut, hB⟩ := h
  exact ⟨ents, entsCutAt_mono hb h0 hcc hc hcut, hB⟩

/-- **One delete of the compaction job at `c₁ ≤ c`** (`kvstore_compaction.go`'s `UnsafeDelete` of
an entry `e` it does not keep, the backend recording it deleted: `X'`) keeps the cut at `c`, given
the job's loop invariant (`hpast`: every entry below `e` deletable at `c₁` already gone), and moves
that invariant past `e` (`entsCutAt_jobStep`). -/
theorem cutAt_del {L : Log} (hb : LogB L) (hwf : LogWf' L) {c c₁ : Int} (h0 : -1 ≤ c₁)
    (hcc : c₁ ≤ c) (hc : c < L.length) {m : Bucket} {X X' : backend.VData} {ents : List KvEnt}
    (hcut : entsCutAt L c ents) (hB : ∀ k, physLookup m X k = (bucketOfEnts ents).lookup k)
    {e : KvEnt} (he : e ∈ logEnts L 0 L.length) (hdel : KeyDel L c₁ (revBytes e.rev e.tomb))
    (hpast : ∀ e' ∈ logEnts L 0 L.length, Rev.lt e'.rev e.rev →
      KeyDel L c₁ (revBytes e'.rev e'.tomb) → e' ∉ ents)
    (hX' : ∀ k, (X'.lookup (keyName, k)).isSome =
      ((X.lookup (keyName, k)).isSome || decide (k = revBytes e.rev e.tomb))) :
    entsCutAt L c (ents.filter (fun x => decide (x.rev ≠ e.rev))) ∧
    (∀ k, physLookup m X' k = (bucketOfEnts (ents.filter (fun x => decide (x.rev ≠ e.rev)))).lookup k) ∧
    ∀ e' ∈ logEnts L 0 L.length, (Rev.lt e'.rev e.rev ∨ e'.rev = e.rev) →
      KeyDel L c₁ (revBytes e'.rev e'.tomb) → e' ∉ ents.filter (fun x => decide (x.rev ≠ e.rev)) := by
  obtain ⟨hcut', hpast'⟩ := entsCutAt_jobStep hb hwf h0 hcc hc hcut he hdel hpast
  refine ⟨hcut', fun k => ?_, hpast'⟩
  have hsl : (ents.filter (fun x => decide (x.rev ≠ e.rev))).Sublist (logEnts L 0 L.length) :=
    List.filter_sublist.trans hcut.1
  have hmemF : ∀ x, x ∈ ents.filter (fun x => decide (x.rev ≠ e.rev)) ↔ x ∈ ents ∧ x.rev ≠ e.rev := by
    intro x; rw [List.mem_filter, decide_eq_true_eq]
  by_cases hk : k = revBytes e.rev e.tomb
  · have hl : physLookup m X' k = none := by
      unfold physLookup; rw [hX', hk]; simp
    rw [hl]; symm
    cases h2 : (bucketOfEnts (ents.filter (fun x => decide (x.rev ≠ e.rev)))).lookup k with
    | none => rfl
    | some v =>
      obtain ⟨x, hx, hpx⟩ := List.mem_map.1 ((bucketOfEnts_lookup_iff L hb hsl k v).1 h2)
      have hxk : revBytes x.rev x.tomb = revBytes e.rev e.tomb := (congrArg Prod.fst hpx).trans hk
      exact absurd (revBytes_inj _ _ _ _ hxk).2 ((hmemF x).1 hx).2
  · have hl : physLookup m X' k = physLookup m X k := by
      unfold physLookup; rw [hX']; simp [hk]
    rw [hl, hB k]
    apply Option.ext
    intro v
    rw [bucketOfEnts_lookup_iff L hb hcut.1 k v, bucketOfEnts_lookup_iff L hb hsl k v]
    constructor
    · intro hm
      obtain ⟨x, hx, hpx⟩ := List.mem_map.1 hm
      refine List.mem_map.2 ⟨x, (hmemF x).2 ⟨hx, fun hr => ?_⟩, hpx⟩
      have hxe := logEnts_rev_inj hb (hcut.1.subset hx) he hr
      subst hxe
      exact hk (congrArg Prod.fst hpx).symm
    · intro hm
      obtain ⟨x, hx, hpx⟩ := List.mem_map.1 hm
      exact List.mem_map.2 ⟨x, ((hmemF x).1 hx).1, hpx⟩

/-! ## The cut under a commit (`storeTxnWrite.End`'s new revision; the snapshot image's item 3) -/

/-- A fold of inserts agrees at `k` on two maps agreeing there, or that it writes at `k`. -/
theorem foldl_ins_lookup (k : GoString) :
    ∀ (l : List (GoString × GoString)) (m₁ m₂ : Bucket),
      (k ∈ l.map Prod.fst ∨ m₁.lookup k = m₂.lookup k) →
      (l.foldl (fun m p => GMap.insert p.1 p.2 m) m₁).lookup k =
        (l.foldl (fun m p => GMap.insert p.1 p.2 m) m₂).lookup k
  | [], m₁, m₂, h => by
    rcases h with h | h
    · simp at h
    · exact h
  | p :: l, m₁, m₂, h => by
    simp only [List.foldl_cons]
    apply foldl_ins_lookup k l
    by_cases hp : p.1 = k
    · right; rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff, if_pos hp, if_pos hp]
    · rcases h with h | h
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hp
        · left; exact h
      · right; rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff, if_neg hp, if_neg hp]; exact h

/-- A fold of inserts that writes nothing at `k` leaves it. -/
theorem foldl_ins_lookup_not (k : GoString) :
    ∀ (l : List (GoString × GoString)) (m : Bucket), k ∉ l.map Prod.fst →
      (l.foldl (fun m p => GMap.insert p.1 p.2 m) m).lookup k = m.lookup k
  | [], m, _ => rfl
  | p :: l, m, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [foldl_ins_lookup_not k l _ h.2, GMap.lookup_insert_eq_iff, if_neg (fun e => h.1 e.symm)]

/-- The new revision's entries are its puts (`pendPuts`). -/
theorem entsOfRev_pairs (L : Log) (pend : List Change) (hne : L ≠ []) :
    (entsOfRev L.length (stateAt (L ++ [pend]) (L.length - 1)) pend).map KvEnt.pair =
      pendPuts L pend := by
  have hl : 0 < L.length := List.length_pos_iff.2 hne
  have hs : stateAt (L ++ [pend]) (L.length - 1) = stateAfter L := by
    rw [stateAt_append_lt L pend (by omega), stateAt_last]
  rw [hs]
  unfold pendPuts bucketOfRev entsOfRev
  rw [List.map_filterMap]
  congr 1
  funext p
  cases changeKv (W64 L.length) (stateAfter L) pend p.2 <;> rfl

/-- **A commit keeps the cut** (`storeTxnWrite.End`'s new revision `pend` above `L`): the physical
bucket gains the revision's entries, whose keys the backend never recorded deleted (`hX`), and the
cut's shape holds of the old entries and the new ones (a new entry is above every old one, and
compaction at `c < |L|` deletes no new entry: `KeyDel_prefix`). -/
theorem cutOk_append {L : Log} {pend : List Change} (hb : LogB (L ++ [pend])) (hne : L ≠ [])
    {m : Bucket} {X : backend.VData} {c : Int} (h0 : -1 ≤ c) (hc : c < L.length)
    (h : cutOk L m X c) (hX : ∀ p ∈ pendPuts L pend, X.lookup (keyName, p.1) = none) :
    cutOk (L ++ [pend]) ((pendPuts L pend).foldl (fun m p => GMap.insert p.1 p.2 m) m) X c := by
  obtain ⟨ents, hcut, hB⟩ := h
  let N := entsOfRev L.length (stateAt (L ++ [pend]) (L.length - 1)) pend
  have hlog : logEnts (L ++ [pend]) 0 (L ++ [pend]).length = logEnts L 0 L.length ++ N := by
    rw [List.length_append, List.length_singleton]; exact logEnts_snoc L pend
  have hL63 : L.length + 1 < 2 ^ 63 := by have := hb.1; simp at this; omega
  -- an old entry's main is below `|L|`, a new one's is `|L|`
  have hold : ∀ e ∈ logEnts L 0 L.length, sint.Z e.rev.main < L.length := by
    intro e he
    obtain ⟨j, i, cc, kv, -, -, hj, -, -, -, -, rfl⟩ := logEnts_entry L 0 L.length e he
    simp only
    have : sint.Z (W64 j) = j := by word
    rw [this]; exact_mod_cast hj
  have hnew : ∀ e ∈ N, sint.Z e.rev.main = L.length := by
    intro e he
    obtain ⟨i, cc, kv, -, -, rfl⟩ := (mem_entsOfRev _ _ _ e).1 he
    simp only
    word
  have hpre : L <+: L ++ [pend] := List.prefix_append _ _
  refine ⟨ents ++ N, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hlog]; exact hcut.1.append (List.Sublist.refl N)
  · intro e he hn
    rw [hlog] at he
    rcases List.mem_append.1 he with he | he
    · have hne' : e ∉ ents := fun h' => hn (List.mem_append_left _ h')
      exact (KeyDel_prefix L (L ++ [pend]) hpre hb c h0 hc _).2 (hcut.2.1 e he hne')
    · exact absurd (List.mem_append_right _ he) hn
  · intro e₁ he₁ e₂ he₂ hk hlt hn₂
    rw [hlog] at he₁ he₂
    have he₂o : e₂ ∈ logEnts L 0 L.length := by
      rcases List.mem_append.1 he₂ with h' | h'
      · exact h'
      · exact absurd (List.mem_append_right _ h') hn₂
    have hn₂' : e₂ ∉ ents := fun h' => hn₂ (List.mem_append_left _ h')
    have hm₂ := hold e₂ he₂o
    have hle : sint.Z e₁.rev.main ≤ sint.Z e₂.rev.main := by
      rcases hlt with h' | ⟨h', -⟩
      · omega
      · rw [h']; exact Int.le_refl _
    intro hm₁
    rcases List.mem_append.1 hm₁ with h' | h'
    · rcases List.mem_append.1 he₁ with he₁o | he₁n
      · exact hcut.2.2 e₁ he₁o e₂ he₂o hk hlt hn₂' h'
      · have := hnew e₁ he₁n; omega
    · have := hnew e₁ h'; omega
  · intro k
    have hpairs : N.map KvEnt.pair = pendPuts L pend := entsOfRev_pairs L pend hne
    have hbe : bucketOfEnts (ents ++ N) =
        (pendPuts L pend).foldl (fun m p => GMap.insert p.1 p.2 m) (bucketOfEnts ents) := by
      unfold bucketOfEnts
      rw [List.map_append, List.foldl_append, hpairs]
    rw [hbe]
    have hk := hB k
    by_cases hx : (X.lookup (keyName, k)).isSome
    · rw [if_pos hx]
      rw [if_pos hx] at hk
      have hnk : k ∉ (pendPuts L pend).map Prod.fst := by
        intro hm
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
        rw [hX p hp] at hx; cases hx
      rw [foldl_ins_lookup_not k _ _ hnk, ← hk]
    · rw [if_neg hx]
      rw [if_neg hx] at hk
      exact foldl_ins_lookup k _ _ _ (Or.inr hk)

/-- **A commit keeps the job's loop invariant** (`cutOk_append`'s entries): the new revision's
entries are above `c₁`, so compaction at `c₁` deletes none of them. -/
theorem jobPast_append {L : Log} {pend : List Change} (hb : LogB (L ++ [pend])) (hne : L ≠ [])
    {c₁ : Int} (h0 : -1 ≤ c₁) (hc : c₁ < L.length) {p : Rev} {ents : List KvEnt}
    (h : jobPast L c₁ p ents) :
    jobPast (L ++ [pend]) c₁ p
      (ents ++ entsOfRev L.length (stateAt (L ++ [pend]) (L.length - 1)) pend) := by
  intro e' he' hlt hd hm
  have hlog : logEnts (L ++ [pend]) 0 (L ++ [pend]).length =
      logEnts L 0 L.length ++ entsOfRev L.length (stateAt (L ++ [pend]) (L.length - 1)) pend := by
    rw [List.length_append, List.length_singleton]; exact logEnts_snoc L pend
  have hL63 : L.length + 1 < 2 ^ 63 := by have := hb.1; simp at this; omega
  have hpre : L <+: L ++ [pend] := List.prefix_append _ _
  have hd' := (KeyDel_prefix L (L ++ [pend]) hpre hb c₁ h0 hc _).1 hd
  rw [hlog] at he'
  have hnewm : ∀ e ∈ entsOfRev L.length (stateAt (L ++ [pend]) (L.length - 1)) pend,
      sint.Z e.rev.main = L.length := by
    intro e he
    obtain ⟨i, cc, kv, -, -, rfl⟩ := (mem_entsOfRev _ _ _ e).1 he
    simp only
    word
  have hdm : ∀ e ∈ entsOfRev L.length (stateAt (L ++ [pend]) (L.length - 1)) pend,
      ¬ KeyDel (L ++ [pend]) c₁ (revBytes e.rev e.tomb) := by
    intro e he hk
    obtain ⟨-, r, t, hr, -, hrc, -⟩ := hk
    have hre := (revBytes_inj _ _ _ _ hr).2
    rw [← hre] at hrc
    have := hnewm e he
    omega
  rcases List.mem_append.1 he' with ho | hn
  · rcases List.mem_append.1 hm with h1 | h1
    · exact h e' ho hlt hd' h1
    · exact hdm e' h1 hd
  · exact hdm e' hn hd

end pure

end snap
end mvcc
end EtcdGrove
end Perennial
