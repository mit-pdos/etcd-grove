/-
**The physical cut of the `Key` bucket** (F2, stage 2, `notes/image-cmp-f2-plan.md`; pure).
Lean-first (no Rocq counterpart).

The backend's physical view of the `Key` bucket, under compaction, is the log's entries cut per key at
a prefix of the ones compaction at the records' revision deletes (`physCut`, over `entsCutAt`,
`InvIndexRestore.lean`). What keeps the shape:

- `KeyDel` grows with the compaction revision (`KeyDel_mono`: a second compaction scheduled while a
  job runs raises the records' revision), and per key it is closed downwards (`KeyDel_down`: an
  earlier entry of a key whose later entry compaction at `c` deletes is deleted too);
- a commit appends a revision's entries, all present (`entsCutAt_snoc`);
- the job at `c` deletes an entry deletable at `c` once every entry below it deletable at `c` is gone
  (its cursor, `cursorDone`; `entsCutAt_del`).

The key index facts underneath: `kiAvail_down` (what compaction at `c'` keeps, if at or below
`c ≤ c'`, is what compaction at `c` keeps) and `kiAvail_above` (a revision above the kept one is
above `c`), both from `compactGen_later` (a generation after `doCompact`'s has every revision above
`c`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreCut
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchScan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open go_etcd_io.etcd.server.v3.storage.mvcc

section pure
variable [GooseExts]

/-! ## The key index: what compaction keeps, at two revisions -/

theorem Rev.lt_asymm' {a b : Rev} (h1 : Rev.lt a b) (h2 : Rev.lt b a) : False := by
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · omega
  · rw [e2] at h1; omega
  · rw [e1] at h2; omega
  · omega

/-- **A generation after `doCompact`'s at `c`** has every revision above `c` (an earlier
generation's tombstone is at or above `c`, and at `c` only with no re-creation at `c`). -/
theorem compactGen_later {ki : KeyIndex} (hs : KiS ki) (c : w64) {i : Nat}
    (hi : compactGenIdx c ki.gens < i) (hlen : i < ki.gens.length) {r : Rev}
    (hr : r ∈ (ki.gens.getD i Gen.empty).revs) : sint.Z c < sint.Z r.main := by
  have hne := hs.wf.ne
  have hstop := compactGenIdx_stop c ki.gens hne
  generalize hgi : compactGenIdx c ki.gens = gi at hi hstop
  rcases hstop with hst | hst
  · omega
  apply Classical.byContradiction
  intro hcr
  have hcr' : sint.Z r.main ≤ sint.Z c := by omega
  have hne_gi : (ki.gens.getD gi Gen.empty).revs ≠ [] := hs.wf.nonlast gi (by omega)
  have ht := getLastD_mem _ Rev.zero hne_gi
  have h1 := Rev.lt_main_le (hs.cross hi hlen ht hr)
  have h2 : sint.Z c ≤ tombZ (ki.gens.getD gi Gen.empty) := by
    apply Classical.byContradiction
    intro hc
    have hc' : tombZ (ki.gens.getD gi Gen.empty) < sint.Z c := by omega
    rw [genAdv_of_lt _ hc'] at hst
    cases hst
  simp only [tombZ] at h2
  have hne1 : (ki.gens.getD (gi + 1) Gen.empty).revs ≠ [] := by
    rcases Nat.lt_or_eq_of_le (show gi + 1 ≤ i by omega) with h' | h'
    · exact hs.wf.nonlast _ (by omega)
    · rw [h']; exact List.ne_nil_of_mem hr
  obtain ⟨f, fs, hf⟩ := List.exists_cons_of_ne_nil hne1
  have hfmem : f ∈ (ki.gens.getD (gi + 1) Gen.empty).revs := by rw [hf]; exact List.mem_cons_self
  have h3 := Rev.lt_main_le (hs.cross (Nat.lt_succ_self gi) (by omega) ht hfmem)
  have h4 : sint.Z f.main ≤ sint.Z r.main := by
    rcases Nat.lt_or_eq_of_le (show gi + 1 ≤ i by omega) with h' | h'
    · exact Rev.lt_main_le (hs.cross h' hlen hfmem hr)
    · subst h'
      have hgs := hs.gen_sorted hlen
      rw [hf] at hgs hr
      rcases List.mem_cons.1 hr with hrf | hrf
      · rw [hrf]; exact Int.le_refl _
      · exact Rev.lt_main_le (List.rel_of_pairwise_cons hgs hrf)
  have hrec : genRecreatedAt c (ki.gens.getD (gi + 1) Gen.empty) = true := by
    unfold genRecreatedAt; rw [hf]; simp only [decide_eq_true_eq]; omega
  have hadv : genAdv c (ki.gens.getD gi Gen.empty) (ki.gens.getD (gi + 1) Gen.empty) = true := by
    unfold genAdv; rw [hrec]
    simp only [Bool.and_true, Bool.or_eq_true, decide_eq_true_eq]
    right; unfold tombZ; omega
  rw [hadv] at hst
  cases hst

/-- **What compaction at `c'` keeps, at or below `c ≤ c'`, compaction at `c` keeps.** -/
theorem kiAvail_down {ki : KeyIndex} (hs : KiS ki) {c c' : w64} (hcc : sint.Z c ≤ sint.Z c')
    {r : Rev} (h : kiAvail c' ki = some r) (hr : sint.Z r.main ≤ sint.Z c) :
    kiAvail c ki = some r := by
  have hne := hs.wf.ne
  have hlt' := compactGenIdx_lt c' ki.gens hne
  have hge := (compactGenIdx_compact_ge hs.wf c c' hcc).1
  unfold kiAvail at h ⊢
  simp only [] at h ⊢
  rcases genWalk_pAbove_spec (ki.gens.getD (compactGenIdx c' ki.gens) Gen.empty).revs c' with
    ⟨h1, -⟩ | ⟨j, hj, hw, -, hafter⟩
  · rw [h1] at h; simp at h
  rw [hw, if_neg (show ((j : Nat) : Int) ≠ -1 by omega)] at h
  simp only [Int.toNat_natCast, Option.some.injEq] at h
  rw [getD_lt _ hj] at h
  subst h
  have hrmem := List.getElem_mem hj
  have hgi : compactGenIdx c ki.gens = compactGenIdx c' ki.gens := by
    rcases Nat.lt_or_eq_of_le hge with hl | he
    · have := compactGen_later hs c hl hlt' hrmem; omega
    · exact he
  rw [hgi]
  rcases genWalk_pAbove_spec (ki.gens.getD (compactGenIdx c' ki.gens) Gen.empty).revs c with
    ⟨h1, h2⟩ | ⟨j0, hj0, hw0, h0le, h0after⟩
  · have := h2 _ hrmem; omega
  · have hjj : j0 = j := by
      rcases Nat.lt_trichotomy j0 j with hl | he | hg
      · have := h0after j hj hl; omega
      · exact he
      · have := hafter j0 hj0 hg; omega
    subst hjj
    rw [hw0, if_neg (show ((j0 : Nat) : Int) ≠ -1 by omega)]
    simp only [Int.toNat_natCast, getD_lt _ hj0]

/-- **A revision of the key index above the one compaction at `c` keeps is above `c`.** -/
theorem kiAvail_above {ki : KeyIndex} (hs : KiS ki) (c : w64) {a r : Rev}
    (ha : kiAvail c ki = some a) (hr : r ∈ kiRevs ki) (hlt : Rev.lt a r) :
    sint.Z c < sint.Z r.main := by
  have hne := hs.wf.ne
  have hglt := compactGenIdx_lt c ki.gens hne
  unfold kiAvail at ha
  simp only [] at ha
  rcases genWalk_pAbove_spec (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs c with
    ⟨h1, -⟩ | ⟨j, hj, hw, -, hafter⟩
  · rw [h1] at ha; simp at ha
  rw [hw, if_neg (show ((j : Nat) : Int) ≠ -1 by omega)] at ha
  simp only [Int.toNat_natCast, Option.some.injEq] at ha
  rw [getD_lt _ hj] at ha
  subst ha
  unfold kiRevs at hr
  rw [List.mem_flatten] at hr
  obtain ⟨rs, hrs, hr⟩ := hr
  rw [List.mem_map] at hrs
  obtain ⟨g, hg, rfl⟩ := hrs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hr' : r ∈ (ki.gens.getD i Gen.empty).revs := by rw [getD_lt _ hi]; exact hr
  rcases Nat.lt_trichotomy i (compactGenIdx c ki.gens) with hl | he | hgt
  · exact (Rev.lt_asymm' hlt (hs.cross hl hglt hr' (List.getElem_mem hj))).elim
  · rw [he] at hr'
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hr'
    have hsorted := hs.gen_sorted hglt
    rcases Nat.lt_trichotomy p j with hpj | hpj | hpj
    · exact (Rev.lt_asymm' hlt (List.pairwise_iff_getElem.1 hsorted p j hp hj hpj)).elim
    · subst hpj; exact (Rev.lt_asymm' hlt hlt).elim
    · exact hafter p hp hpj
  · exact compactGen_later hs c hgt hi hr'

/-! ## `KeyDel`: monotone in the revision, closed downwards per key -/

/-- **`KeyDel` grows with the compaction revision.** -/
theorem KeyDel_mono {L : Log} (hb : LogB L) {c c' : Int} (hc0 : -1 ≤ c) (hcc : c ≤ c')
    (hc' : c' < L.length) {key : GoString} (h : KeyDel L c key) : KeyDel L c' key := by
  obtain ⟨-, r, t, hk, h0, h1, hkeep⟩ := h
  have hl := hb.1
  have hw : sint.Z (W64 c) = c := by word
  have hw' : sint.Z (W64 c') = c' := by word
  refine ⟨hc', r, t, hk, h0, by omega, fun ⟨k, hka⟩ => hkeep ⟨k, ?_⟩⟩
  exact kiAvail_down (kiOfKey_KiS L hb k) (by rw [hw, hw']; exact hcc) hka (by rw [hw]; exact h1)

/-- **A bucket entry's event**: of the same revision and key. -/
theorem logEnts_ev {L : Log} {e : KvEnt} (he : e ∈ logEnts L 0 L.length) :
    ∃ ev ∈ evsOf L, ev.rev = e.rev ∧ ev.key = e.kv.key := by
  obtain ⟨j, i, c, kv, -, -, -, hgj, -, hc, hkv, rfl⟩ := logEnts_entry L 0 L.length e he
  refine ⟨⟨⟨W64 j, W64 i⟩, c⟩, ?_, rfl, ?_⟩
  · unfold evsOf
    rw [List.mem_flatten]
    refine ⟨evsOfRev j (L.getD j []), List.mem_map.2 ⟨(L.getD j [], j), ?_, rfl⟩, ?_⟩
    · rw [List.mem_zipIdx_iff_getElem?]; exact hgj
    · unfold evsOfRev
      rw [List.mem_map]
      refine ⟨(c, i), ?_, rfl⟩
      rw [List.mem_zipIdx_iff_getElem?]; exact hc
  · show c.key = kv.key
    unfold changeKv at hkv
    rw [hc] at hkv
    cases c with
    | put k v l => simp only at hkv; exact (findKey_key hkv).symm
    | del k => cases hkv; rfl

/-- **`KeyDel` is closed downwards per key**: an earlier entry of a key whose later entry
compaction at `c` deletes is one it deletes. -/
theorem KeyDel_down {L : Log} (hb : LogB L) (hwf : LogWf' L) {c : Int} {e₁ e₂ : KvEnt}
    (h₁ : e₁ ∈ logEnts L 0 L.length) (h₂ : e₂ ∈ logEnts L 0 L.length)
    (hk : e₁.kv.key = e₂.kv.key) (hlt : Rev.lt e₁.rev e₂.rev)
    (hd : KeyDel L c (revBytes e₂.rev e₂.tomb)) : KeyDel L c (revBytes e₁.rev e₁.tomb) := by
  obtain ⟨hcL, r, t, hrb, h0, h1, hkeep⟩ := hd
  obtain ⟨-, rfl⟩ := revBytes_inj _ _ _ _ hrb
  have hl := hb.1
  have hm1 := Rev.lt_main_le hlt
  refine ⟨hcL, e₁.rev, e₁.tomb, rfl, ?_, by omega, ?_⟩
  · exact (logEnts_bounds L hb.1 hb.2 0 L.length (Nat.le_refl _) e₁ h₁).1
  rintro ⟨k', hka⟩
  obtain ⟨ev, hev, hevr, hevk⟩ := kiRevs_kiOfKey (kiAvail_mem hka)
  obtain ⟨ev₁, hev₁, hr₁, hk₁⟩ := logEnts_ev h₁
  have hee := evsOf_rev_inj L hb hev hev₁ (hevr.trans hr₁.symm)
  obtain ⟨ev₂, hev₂, hr₂, hk₂⟩ := logEnts_ev h₂
  have hkey : ev₂.key = k' := by rw [hk₂, ← hk, ← hk₁, ← hee, hevk]
  have hm2 : e₂.rev ∈ kiRevs (kiOfKey (evsOf L) k') := by
    have := ev_mem_kiRevs L hwf hb.1 hb.2 ev₂ hev₂
    rw [hkey, hr₂] at this
    exact this
  have hc' := kiAvail_above (kiOfKey_KiS L hb k') (W64 c) hka hm2 hlt
  have hw : sint.Z (W64 c) = c := by word
  omega

/-! ## The cut: kept by a commit, a later revision, the job's delete -/

/-- **A later compaction revision keeps the cut** (`KeyDel_mono`). -/
theorem entsCutAt_mono {L : Log} (hb : LogB L) {c c' : Int} (hc0 : -1 ≤ c) (hcc : c ≤ c')
    (hc' : c' < L.length) {ents : List KvEnt} (h : entsCutAt L c ents) : entsCutAt L c' ents :=
  ⟨h.1, fun e he hn => KeyDel_mono hb hc0 hcc hc' (h.2.1 e he hn), h.2.2⟩

/-- The entries of a revision appended to `L` (`logEnts_snoc`'s). -/
abbrev snocEnts (L : Log) (cs : List Change) : List KvEnt :=
  entsOfRev L.length (stateAt (L ++ [cs]) (L.length - 1)) cs

theorem logEnts_snoc' (L : Log) (cs : List Change) :
    logEnts (L ++ [cs]) 0 (L ++ [cs]).length = logEnts L 0 L.length ++ snocEnts L cs := by
  rw [List.length_append, List.length_singleton]; exact logEnts_snoc L cs

/-- An appended revision's entries are at its revision, above the log's. -/
theorem snocEnts_main {L : Log} {cs : List Change} (hb : LogB (L ++ [cs])) {e : KvEnt}
    (he : e ∈ snocEnts L cs) : sint.Z e.rev.main = L.length := by
  obtain ⟨i, c, kv, -, -, rfl⟩ := (mem_entsOfRev _ _ _ _).1 he
  have hl := hb.1
  simp only [List.length_append, List.length_singleton] at hl
  show sint.Z (W64 (L.length : Int)) = L.length
  word

/-- **A commit keeps the cut**: the appended revision's entries are all present. -/
theorem entsCutAt_snoc {L : Log} {cs : List Change} (hb : LogB (L ++ [cs])) {c : Int}
    (hc0 : -1 ≤ c) (hc : c < L.length) {ents : List KvEnt} (h : entsCutAt L c ents) :
    entsCutAt (L ++ [cs]) c (ents ++ snocEnts L cs) := by
  have hbL := hb.prefix
  have hpre : L <+: L ++ [cs] := List.prefix_append L [cs]
  have hold : ∀ e ∈ logEnts L 0 L.length, sint.Z e.rev.main ≤ (L.length : Int) - 1 :=
    logEnts_main_le L hbL
  unfold entsCutAt
  rw [logEnts_snoc']
  refine ⟨h.1.append (List.Sublist.refl _), fun e he hn => ?_, fun e₁ h₁ e₂ h₂ hk hlt hn => ?_⟩
  · rcases List.mem_append.1 he with he | he
    · exact (KeyDel_prefix L (L ++ [cs]) hpre hb c hc0 hc _).2
        (h.2.1 e he (fun h' => hn (List.mem_append_left _ h')))
    · exact absurd (List.mem_append_right _ he) hn
  · have h₂o : e₂ ∈ logEnts L 0 L.length := by
      rcases List.mem_append.1 h₂ with h | h
      · exact h
      · exact absurd (List.mem_append_right _ h) hn
    have hn₂ : e₂ ∉ ents := fun h' => hn (List.mem_append_left _ h')
    have hm := hold e₂ h₂o
    have hm1 := Rev.lt_main_le hlt
    have h₁n : e₁ ∉ snocEnts L cs := fun h' => by have := snocEnts_main hb h'; omega
    have h₁o : e₁ ∈ logEnts L 0 L.length := by
      rcases List.mem_append.1 h₁ with h | h
      · exact h
      · exact absurd h h₁n
    intro h'
    rcases List.mem_append.1 h' with h' | h'
    · exact h.2.2 e₁ h₁o e₂ h₂o hk hlt hn₂ h'
    · exact h₁n h'

/-- The entries but the one at `e`'s revision. -/
def entsDel (ents : List KvEnt) (e : KvEnt) : List KvEnt :=
  ents.filter fun x => decide (x.rev ≠ e.rev)

theorem mem_entsDel {ents : List KvEnt} {e x : KvEnt} :
    x ∈ entsDel ents e ↔ x ∈ ents ∧ x.rev ≠ e.rev := by
  unfold entsDel; simp

/-- **The job's delete keeps the cut**: the job at `c` (at or below the cut's revision) deletes an
entry `e` compaction at `c` deletes, every entry below it that compaction at `c` deletes gone
(the job's cursor). -/
theorem entsCutAt_del {L : Log} (hb : LogB L) (hwf : LogWf' L) {c crev : Int} (hc0 : -1 ≤ c)
    (hcc : c ≤ crev) (hcr : crev < L.length) {ents : List KvEnt} (h : entsCutAt L crev ents)
    {e : KvEnt} (he : e ∈ logEnts L 0 L.length) (hd : KeyDel L c (revBytes e.rev e.tomb))
    (hdone : ∀ e' ∈ logEnts L 0 L.length, KeyDel L c (revBytes e'.rev e'.tomb) →
      Rev.lt e'.rev e.rev → e' ∉ ents) :
    entsCutAt L crev (entsDel ents e) := by
  have hinj : ∀ x ∈ logEnts L 0 L.length, x.rev = e.rev → x = e :=
    fun x hx hr => logEnts_rev_inj hb hx he hr
  refine ⟨List.filter_sublist.trans h.1,
    fun x hx hn => ?_, fun e₁ h₁ e₂ h₂ hk hlt hn => ?_⟩
  · by_cases hxe : x.rev = e.rev
    · rw [hinj x hx hxe]; exact KeyDel_mono hb hc0 hcc hcr hd
    · exact h.2.1 x hx (fun h' => hn (mem_entsDel.2 ⟨h', hxe⟩))
  · intro h₁'
    obtain ⟨h₁e, h₁r⟩ := mem_entsDel.1 h₁'
    by_cases h₂e : e₂.rev = e.rev
    · have := hinj e₂ h₂ h₂e
      subst this
      exact hdone e₁ h₁ (KeyDel_down hb hwf h₁ h₂ hk hlt hd) hlt h₁e
    · have hn₂ : e₂ ∉ ents := fun h' => hn (mem_entsDel.2 ⟨h', h₂e⟩)
      exact h.2.2 e₁ h₁ e₂ h₂ hk hlt hn₂ h₁e

end pure

end mvcc
end EtcdGrove
end Perennial
