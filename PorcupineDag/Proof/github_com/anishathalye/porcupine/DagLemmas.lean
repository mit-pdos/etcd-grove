/- Lean-first (no Rocq counterpart).

# Pure lemmas of `chains.lift`, `chains.unlift` and `checkSingle` (2026-11-02)

The frontier's members are the unfinished clients without dependency (`frontier_iff`, from
`ChainsInv`'s candidate list and `cand_iff`); a frame's client (`clientOf_eq`); and the loop
invariants of the `j`-loops of `chains.unlift` (`UnliftInv`) and `chains.lift` (`LiftInv`), with
their initial, step and final lemmas.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.ChainsOwn

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial
namespace github_com.anishathalye.porcupine

open Theory

variable {α : Type}

theorem snat_eq (x : w64) : sint.nat x = (sint.Z x).toNat := rfl

section basic
variable {h : List (Op α)} {cs : List (List Nat)}

theorem opAt_get {c k : Nat} (hk : k < (chain cs c).length) :
    (chain cs c)[k]? = some (opAt cs c k) := by
  rw [opAt_eq hk]; exact List.getElem?_eq_getElem hk

theorem chain_eq {c : Nat} (hc : c < cs.length) : chain cs c = cs[c] := by
  unfold chain; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]

/-- The client whose chain holds `y`. -/
theorem clientOf_eq (hok : ChainsOk h cs) {c y : Nat} (hc : c < cs.length)
    (hy : y ∈ chain cs c) : clientOf cs y = c := by
  unfold clientOf
  rw [List.findIdx_eq hc]
  refine ⟨by rw [← chain_eq hc]; simpa using hy, fun j hj => decide_eq_false fun hyj => ?_⟩
  have hj' : y ∈ chain cs j := by rw [chain_eq (by omega)]; exact hyj
  have := hok.2.2 y j c hj' hy
  omega

theorem chain_length_le (hok : ChainsOk h cs) (c : Nat) : (chain cs c).length ≤ h.length := by
  have hs : chain cs c ⊆ List.range h.length := fun y hy => List.mem_range.mpr (lt_length_of_mem hok hy)
  simpa using List.Nodup.length_le_of_subset (hok.1 c).1 hs

theorem keyGt_irrefl {y : Nat} : ¬ KeyGt h cs y y := fun hk => keyGt_asymm hk hk

/-- A frontier sorted by `KeyGt` (through the heads) has no duplicate. -/
theorem nodup_of_sorted {f : Nat → Nat} {l : List Nat} (hp : (l.map f).Pairwise (KeyGt h cs)) :
    l.Nodup := by
  have := List.pairwise_map.mp hp
  exact this.imp fun {a b} hk (he : a = b) => keyGt_irrefl (he ▸ hk)

/-- The frontier: the unfinished clients without dependency. -/
theorem frontier_iff (hok : ChainsOk h cs) (hwf : CallLeRet h) {B : List Nat} {st : ChSt}
    (hci : ChainsInv h cs B st) (x : Nat) :
    x ∈ st.frontier ↔ x < cs.length ∧ st.head x < (chain cs x).length ∧
      deps h cs st.heads x = 0 := by
  obtain ⟨_, _, hpos, _, hclos, hlt, _, _, _, hfrm, hcl⟩ := hci
  have hB := ids_iff_headsSet hok hpos hlt
  have hcand := fun y => cand_iff (y := y) hok hwf hB hclos
  constructor
  · intro hx
    obtain ⟨hxl, hxh⟩ := hfrm x hx
    have hm : hdOp cs st x ∈ frOf cs st := List.mem_map_of_mem hx
    obtain ⟨c', hc', hc'l, hop, hd⟩ := (hcand _).mp ((hcl.2 _).mp hm)
    have := pos_unique hok (opAt_get hc'l) (by rw [hop]; exact opAt_get hxh)
    obtain ⟨rfl, -⟩ := this
    exact ⟨hxl, hxh, hd⟩
  · rintro ⟨hxl, hxh, hd⟩
    have hc : Cand h (Before h cs) B (hdOp cs st x) := (hcand _).mpr ⟨x, hxl, hxh, rfl, hd⟩
    obtain ⟨x', hx', he⟩ := List.mem_map.mp ((hcl.2 _).mpr hc)
    obtain ⟨_, hx'h⟩ := hfrm x' hx'
    have := pos_unique hok (opAt_get hx'h) (by
      have : opAt cs x' (st.head x') = opAt cs x (st.head x) := he
      rw [this]; exact opAt_get hxh)
    obtain ⟨rfl, -⟩ := this
    exact hx'

/-- Every head at its chain's end: every operation is linearized. -/
theorem complete_all (hok : ChainsOk h cs) {B : List Nat} {st : ChSt} (hci : ChainsInv h cs B st)
    (hall : ∀ c, c < cs.length → st.head c = (chain cs c).length) :
    ∀ y, y < h.length → y ∈ B := by
  intro y hy
  obtain ⟨c, hc, hyc⟩ := (hok.2.1 y).mp hy
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hyc
  have := (hci.2.2.1 c k hk).mpr (by have := hall c hc; unfold ChSt.head at this; omega)
  rw [hke] at this; exact this

/-- Some head before its chain's end: some operation is not linearized. -/
theorem incomplete_some (hok : ChainsOk h cs) {B : List Nat} {st : ChSt} (hci : ChainsInv h cs B st)
    (hnot : ¬ ∀ c, c < cs.length → st.head c = (chain cs c).length) :
    ∃ y, y < h.length ∧ y ∉ B := by
  have : ∃ c, c < cs.length ∧ st.head c ≠ (chain cs c).length := by
    refine Classical.byContradiction fun hn => hnot fun c hc => ?_
    exact Classical.byContradiction fun hne => hn ⟨c, hc, hne⟩
  obtain ⟨c, hc, hne⟩ := this
  have hle : st.head c ≤ (chain cs c).length := by
    have := hci.2.2.2.1.2 c; unfold ChSt.head; exact this
  have hlt : st.head c < (chain cs c).length := by omega
  refine ⟨(chain cs c)[st.head c], lt_length_of_mem hok (List.getElem_mem hlt), fun hB => ?_⟩
  have := (hci.2.2.1 c (st.head c) hlt).mp hB
  unfold ChSt.head at this; omega

end basic

/-! ## `chains.unlift` -/

section unlift
variable {σ : Type} {h : List (Op α)} {cs : List (List Nat)}

/-- What `chains.unlift` knows at its start: the frame `f` lifted the head `H'[c]` of client `c`
at the heads `H'` of the frames below. -/
def UnliftCtx (h : List (Op α)) (cs : List (List Nat)) (st : ChSt) (H' : List Nat) (c : Nat)
    (f : Frame σ) (fs : List (Frame σ)) : Prop :=
  ChainsOk h cs ∧ CallLeRet h ∧ ChainsInv h cs (ids (f :: fs)) st ∧
  FramesStruct h cs (Before h cs) (f :: fs) ∧ c < cs.length ∧
  H'.getD c 0 < (chain cs c).length ∧ opAt cs c (H'.getD c 0) = f.id ∧
  st.heads = H'.set c (H'.getD c 0 + 1) ∧ H' = headsOf cs (ids fs)

/-- The `j`-loop's invariant (clients below `j` processed). -/
def UnliftInv (h : List (Op α)) (cs : List (List Nat)) (st : ChSt) (H' : List Nat) (c j : Nat)
    (stc : ChSt) : Prop :=
  stc.heads = H' ∧ stc.vis = st.vis ∧ stc.fu = st.fu ∧ stc.nDeps.length = st.nDeps.length ∧
  stc.nDeps.getD c 0 = 0 ∧
  (∀ d, d ≠ c → d < j → d < cs.length → H'.getD d 0 < (chain cs d).length →
    sint.Z (stc.nDeps.getD d 0) = deps h cs H' d) ∧
  (∀ d, d ≠ c → j ≤ d → stc.nDeps.getD d 0 = st.nDeps.getD d 0) ∧
  stc.frontier.Sublist st.frontier ∧
  (∀ x, x ∈ stc.frontier ↔ x ≠ c ∧ x ∈ st.frontier ∧ (x < j → deps h cs H' x = 0))

section ctx
variable {st : ChSt} {H' : List Nat} {c : Nat} {f : Frame σ} {fs : List (Frame σ)}

theorem UnliftCtx.H'_length (hx : UnliftCtx h cs st H' c f fs) : H'.length = cs.length := by
  rw [hx.2.2.2.2.2.2.2.2]; exact headsOf_length

theorem UnliftCtx.head_ne (hx : UnliftCtx h cs st H' c f fs) {d : Nat} (hd : d ≠ c) :
    st.head d = H'.getD d 0 := by
  unfold ChSt.head
  rw [hx.2.2.2.2.2.2.2.1, set_getD (by rw [hx.H'_length]; exact hx.2.2.2.2.1)]
  simp [hd]

theorem UnliftCtx.head_c (hx : UnliftCtx h cs st H' c f fs) : st.head c = H'.getD c 0 + 1 := by
  unfold ChSt.head
  rw [hx.2.2.2.2.2.2.2.1, set_getD (by rw [hx.H'_length]; exact hx.2.2.2.2.1)]
  simp

/-- The heads after the client's `head--`. -/
theorem UnliftCtx.heads_dec (hx : UnliftCtx h cs st H' c f fs) :
    st.heads.set c (st.head c - 1) = H' := by
  have hc : c < H'.length := by rw [hx.H'_length]; exact hx.2.2.2.2.1
  rw [hx.head_c, Nat.add_sub_cancel, hx.2.2.2.2.2.2.2.1, List.set_set,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some, List.set_getElem_self]

/-- The frames below: their heads are `H'`, and `B = ids fs` is as `cand_iff` needs. -/
theorem UnliftCtx.below (hx : UnliftCtx h cs st H' c f fs) :
    (∀ y, y ∈ ids fs ↔ headsSet cs H' y) ∧ (∀ z w, w ∈ ids fs → Before h cs z w → z ∈ ids fs) := by
  obtain ⟨hok, hwf, _, hfs, _, _, _, _, hH'⟩ := hx
  obtain ⟨hpos, _⟩ := heads_ids hok hwf hfs.1
  rw [← hH'] at hpos
  exact ⟨ids_iff_headsSet hok hpos (framesStruct_lt hfs.1),
    fun z w hw hzw => framesStruct_below hfs.1 w hw z hzw⟩

theorem UnliftCtx.cand_iff' (hx : UnliftCtx h cs st H' c f fs) (y : Nat) :
    Cand h (Before h cs) (ids fs) y ↔ ∃ d, d < cs.length ∧ H'.getD d 0 < (chain cs d).length ∧
      opAt cs d (H'.getD d 0) = y ∧ deps h cs H' d = 0 :=
  cand_iff hx.1 hx.2.1 hx.below.1 hx.below.2

theorem UnliftCtx.deps_c (hx : UnliftCtx h cs st H' c f fs) : deps h cs H' c = 0 := by
  obtain ⟨d, _, hdl, hop, hd⟩ := (hx.cand_iff' f.id).mp (framesStruct_cand hx.2.2.2.1)
  obtain ⟨rfl, -⟩ := pos_unique hx.1 (opAt_get hdl)
    (by rw [hop, ← hx.2.2.2.2.2.2.1]; exact opAt_get hx.2.2.2.2.2.1)
  exact hd

/-- `deps_lift` read backwards. -/
theorem UnliftCtx.deps_ne (hx : UnliftCtx h cs st H' c f fs) {d : Nat} (hd : d ≠ c) :
    deps h cs H' d = deps h cs st.heads d +
      (if H'.getD d 0 < (chain cs d).length ∧ FUe h cs d c (H'.getD d 0) = H'.getD c 0 + 1
       then 1 else 0) := by
  rw [hx.2.2.2.2.2.2.2.1]
  exact deps_lift hd (by rw [hx.H'_length]; exact hx.2.2.2.2.1)

theorem deps_le {H : List Nat} {d : Nat} : deps h cs H d ≤ cs.length := by
  unfold deps
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem UnliftCtx.nDeps_ne (hx : UnliftCtx h cs st H' c f fs) {d : Nat} (hd : d ≠ c)
    (hdl : d < cs.length) (hdh : H'.getD d 0 < (chain cs d).length) :
    sint.Z (st.nDeps.getD d 0) = deps h cs st.heads d := by
  have := hx.2.2.1.2.2.2.2.2.2.2.2.1 d hdl (by rw [hx.head_ne hd]; exact hdh)
  exact this

theorem UnliftCtx.frontier_iff' (hx : UnliftCtx h cs st H' c f fs) (x : Nat) :
    x ∈ st.frontier ↔ x < cs.length ∧ st.head x < (chain cs x).length ∧
      deps h cs st.heads x = 0 :=
  frontier_iff hx.1 hx.2.1 hx.2.2.1 x

theorem UnliftCtx.shape (hx : UnliftCtx h cs st H' c f fs) {stc : ChSt}
    (hh : stc.heads = H') (hv : stc.vis = st.vis) (hf : stc.fu = st.fu)
    (hn : stc.nDeps.length = st.nDeps.length) : ShapeOk cs stc := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx.2.2.1.1
  refine ⟨by rw [hh, hx.H'_length], by rw [hn, h2], by rw [hv, h3], by rw [hf, h4], ?_⟩
  intro c' k hk
  unfold ChSt.fuAt
  rw [hv, hf]
  exact h5 c' k hk

theorem UnliftCtx.inv_init (hx : UnliftCtx h cs st H' c f fs) {stc : ChSt}
    (hh : stc.heads = H') (hv : stc.vis = st.vis) (hf : stc.fu = st.fu)
    (hn : stc.nDeps = st.nDeps.set c (W64 0)) (hfr : stc.frontier = st.frontier.erase c) :
    UnliftInv h cs st H' c 0 stc := by
  have hcn : c < st.nDeps.length := by rw [hx.2.2.1.1.2.1]; exact hx.2.2.2.2.1
  have hnd : st.frontier.Nodup := nodup_of_sorted hx.2.2.1.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hh, hv, hf, by rw [hn, List.length_set], ?_, fun d _ hd => absurd hd (Nat.not_lt_zero _),
    fun d hd _ => ?_, by rw [hfr]; exact List.erase_sublist, fun x => ?_⟩
  · rw [hn]; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hcn]
  · rw [hn]; simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hd)]
  · rw [hfr, hnd.mem_erase_iff]
    exact ⟨fun ⟨a, b⟩ => ⟨a, b, fun h0 => absurd h0 (Nat.not_lt_zero _)⟩, fun ⟨a, b, _⟩ => ⟨a, b⟩⟩

theorem UnliftCtx.inv_skip (hx : UnliftCtx h cs st H' c f fs) {j : Nat} {stc : ChSt}
    (hi : UnliftInv h cs st H' c j stc)
    (hcond : j = c ∨ ¬ H'.getD j 0 < (chain cs j).length ∨
      FUe h cs j c (H'.getD j 0) ≠ H'.getD c 0 + 1) :
    UnliftInv h cs st H' c (j + 1) stc := by
  obtain ⟨hh, hv, hf, hn, hnc, hlo, hhi, hsub, hmem⟩ := hi
  refine ⟨hh, hv, hf, hn, hnc, fun d hdc hd hdl hdh => ?_, fun d hdc hd => hhi d hdc (by omega),
    hsub, fun x => ?_⟩
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
    · exact hlo d hdc hd hdl hdh
    · rw [hhi d hdc (Nat.le_refl _), hx.nDeps_ne hdc hdl hdh, hx.deps_ne hdc]
      have : ¬ (H'.getD d 0 < (chain cs d).length ∧ FUe h cs d c (H'.getD d 0) = H'.getD c 0 + 1) := by
        rintro ⟨h1, h2⟩
        rcases hcond with h0 | h0 | h0
        · exact hdc h0
        · exact h0 h1
        · exact h0 h2
      rw [if_neg this, Nat.add_zero]
  · rw [hmem x]
    constructor
    · rintro ⟨hxc, hxf, hxd⟩
      refine ⟨hxc, hxf, fun hxj => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hxj) with hxj | rfl
      · exact hxd hxj
      · obtain ⟨_, hxh, hdx⟩ := (hx.frontier_iff' x).mp hxf
        rw [hx.deps_ne hxc, hdx]
        rw [hx.head_ne hxc] at hxh
        have : ¬ (H'.getD x 0 < (chain cs x).length ∧ FUe h cs x c (H'.getD x 0) = H'.getD c 0 + 1) := by
          rintro ⟨h1, h2⟩
          rcases hcond with h0 | h0 | h0
          · exact hxc h0
          · exact h0 h1
          · exact h0 h2
        rw [if_neg this]
    · rintro ⟨hxc, hxf, hxd⟩
      exact ⟨hxc, hxf, fun hxj => hxd (by omega)⟩

theorem UnliftCtx.inv_hit (hx : UnliftCtx h cs st H' c f fs) {j : Nat} {stc stc' : ChSt}
    (hi : UnliftInv h cs st H' c j stc) (hjc : j ≠ c) (hjl : j < cs.length)
    (hjh : H'.getD j 0 < (chain cs j).length) (hfu : FUe h cs j c (H'.getD j 0) = H'.getD c 0 + 1)
    (hcs : (cs.length : Int) < 2 ^ 62)
    (hh' : stc'.heads = stc.heads) (hv' : stc'.vis = stc.vis) (hf' : stc'.fu = stc.fu)
    (hn' : stc'.nDeps = stc.nDeps.set j (stc.nDeps.getD j 0 + W64 1))
    (hfr' : stc'.frontier = if stc.nDeps.getD j 0 = W64 0 then stc.frontier.erase j else stc.frontier) :
    UnliftInv h cs st H' c (j + 1) stc' := by
  obtain ⟨hh, hv, hf, hn, hnc, hlo, hhi, hsub, hmem⟩ := hi
  have hjn : j < stc.nDeps.length := by rw [hn, hx.2.2.1.1.2.1]; exact hjl
  have hold : stc.nDeps.getD j 0 = st.nDeps.getD j 0 := hhi j hjc (Nat.le_refl _)
  have hz : sint.Z (stc.nDeps.getD j 0) = deps h cs st.heads j := by
    rw [hold]; exact hx.nDeps_ne hjc hjl hjh
  have hdj : deps h cs H' j = deps h cs st.heads j + 1 := by
    rw [hx.deps_ne hjc, if_pos ⟨hjh, hfu⟩]
  have hdle : deps h cs st.heads j ≤ cs.length := deps_le
  have hget : ∀ d, stc'.nDeps.getD d 0 =
      if d = j then stc.nDeps.getD j 0 + W64 1 else stc.nDeps.getD d 0 := by
    intro d
    rw [hn']
    by_cases hdj' : d = j
    · subst hdj'; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hjn]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hdj'), hdj']
  have hnd : stc.frontier.Nodup := (nodup_of_sorted hx.2.2.1.2.2.2.2.2.2.2.2.2.2.1).sublist hsub
  refine ⟨by rw [hh', hh], by rw [hv', hv], by rw [hf', hf], by rw [hn', List.length_set, hn], ?_,
    fun d hdc hd hdl hdh => ?_, fun d hdc hd => ?_, ?_, fun x => ?_⟩
  · rw [hget c, if_neg (Ne.symm hjc), hnc]
  · rw [hget d]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
    · rw [if_neg (show d ≠ j by omega)]; exact hlo d hdc hd hdl hdh
    · simp only [↓reduceIte]
      rw [hdj]
      have h2 : (deps h cs st.heads d : Int) ≤ cs.length := by exact_mod_cast hdle
      have : sint.Z (stc.nDeps.getD d 0 + W64 1) = sint.Z (stc.nDeps.getD d 0) + 1 := by
        have h1 := hz
        word
      rw [this, hz]; push_cast; rfl
  · rw [hget d, if_neg (show d ≠ j by omega), hhi d hdc (by omega)]
  · rw [hfr']; split
    · exact (List.erase_sublist).trans hsub
    · exact hsub
  · have hjst : j ∈ st.frontier → stc.nDeps.getD j 0 = W64 0 := by
      intro hjf
      obtain ⟨_, _, hd0⟩ := (hx.frontier_iff' j).mp hjf
      rw [hd0] at hz
      have := hz
      word
    rw [hfr']
    split
    · rw [hnd.mem_erase_iff, hmem x]
      constructor
      · rintro ⟨hxj, hxc, hxf, hxd⟩
        exact ⟨hxc, hxf, fun hx1 => hxd (by omega)⟩
      · rintro ⟨hxc, hxf, hxd⟩
        have hxj : x ≠ j := by rintro rfl; have := hxd (by omega); omega
        exact ⟨hxj, hxc, hxf, fun hx1 => hxd (by omega)⟩
    · rename_i h0
      rw [hmem x]
      constructor
      · rintro ⟨hxc, hxf, hxd⟩
        refine ⟨hxc, hxf, fun hx1 => ?_⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx1) with hx1 | rfl
        · exact hxd hx1
        · exact absurd (hjst hxf) h0
      · rintro ⟨hxc, hxf, hxd⟩
        exact ⟨hxc, hxf, fun hx1 => hxd (by omega)⟩

/-- `addToFrontier(c)`'s premises at the loop's end. -/
theorem UnliftCtx.add_pre (hx : UnliftCtx h cs st H' c f fs) {stc : ChSt}
    (hi : UnliftInv h cs st H' c cs.length stc) :
    ShapeOk cs stc ∧ c ∉ stc.frontier ∧ stc.head c < (chain cs c).length ∧
    hdOp cs stc c = f.id ∧
    (∀ v ∈ stc.frontier, v < cs.length ∧ stc.head v < (chain cs v).length ∧
      ¬ Prec h (hdOp cs stc c) (hdOp cs stc v) ∧ ¬ Prec h (hdOp cs stc v) (hdOp cs stc c)) ∧
    (frOf cs stc).Pairwise (KeyGt h cs) := by
  obtain ⟨hh, hv, hf, hn, hnc, hlo, hhi, hsub, hmem⟩ := hi
  have hhead : ∀ d, stc.head d = H'.getD d 0 := fun d => by unfold ChSt.head; rw [hh]
  have hcf : Cand h (Before h cs) (ids fs) f.id := framesStruct_cand hx.2.2.2.1
  have hcop : hdOp cs stc c = f.id := by unfold hdOp; rw [hhead]; exact hx.2.2.2.2.2.2.1
  have hmemv : ∀ v ∈ stc.frontier, v ≠ c ∧ v < cs.length ∧ H'.getD v 0 < (chain cs v).length ∧
      deps h cs H' v = 0 := by
    intro v hvf
    obtain ⟨hvc, hvst, hvd⟩ := (hmem v).mp hvf
    obtain ⟨hvl, hvh, _⟩ := (hx.frontier_iff' v).mp hvst
    rw [hx.head_ne hvc] at hvh
    exact ⟨hvc, hvl, hvh, hvd hvl⟩
  refine ⟨hx.shape hh hv hf hn, fun hc => ((hmem c).mp hc).1 rfl,
    by rw [hhead]; exact hx.2.2.2.2.2.1, hcop, fun v hvf => ?_, ?_⟩
  · obtain ⟨hvc, hvl, hvh, hvd⟩ := hmemv v hvf
    have hcv : Cand h (Before h cs) (ids fs) (hdOp cs stc v) :=
      (hx.cand_iff' _).mpr ⟨v, hvl, hvh, by unfold hdOp; rw [hhead], hvd⟩
    rw [hcop]
    exact ⟨hvl, by rw [hhead]; exact hvh, fun hp => cand_not_prec hcf hcv (Or.inl hp),
      fun hp => cand_not_prec hcv hcf (Or.inl hp)⟩
  · have heq : frOf cs stc = stc.frontier.map (hdOp cs st) := by
      unfold frOf
      refine List.map_congr_left fun v hvf => ?_
      unfold hdOp
      rw [hhead, hx.head_ne (hmemv v hvf).1]
    rw [heq]
    exact hx.2.2.1.2.2.2.2.2.2.2.2.2.2.1.sublist (hsub.map _)

/-- The loop's end and `addToFrontier(c)`: the chains' invariant of the frames below, and the
frontier is the frame's candidate list. -/
theorem UnliftCtx.inv_final (hx : UnliftCtx h cs st H' c f fs) {stc : ChSt} {fr' : List Nat}
    (hi : UnliftInv h cs st H' c cs.length stc)
    (hp : (fr'.map (hdOp cs stc)).Pairwise (KeyGt h cs))
    (hm : ∀ x, x ∈ fr' ↔ x = c ∨ x ∈ stc.frontier) :
    ChainsInv h cs (ids fs) { stc with frontier := fr' } ∧
      frOf cs { stc with frontier := fr' } = f.fr := by
  obtain ⟨hok, hwf, hci, hfs, hc, hcl, hcop, hHH, hH'⟩ := hx
  have hx : UnliftCtx h cs st H' c f fs := ⟨hok, hwf, hci, hfs, hc, hcl, hcop, hHH, hH'⟩
  obtain ⟨hh, hv, hf, hn, hnc, hlo, hhi, hsub, hmem⟩ := hi
  have hhead : ∀ d, ChSt.head { stc with frontier := fr' } d = H'.getD d 0 :=
    fun d => by unfold ChSt.head; simp only; rw [hh]
  obtain ⟨hpos, hHo⟩ := heads_ids hok hwf hfs.1
  rw [← hH'] at hpos hHo
  have hfu := hci.2.2.2.2.2.2.1
  have hvis := hci.2.2.2.2.2.2.2.1
  have hmem' : ∀ x, x ∈ fr' ↔ x < cs.length ∧ H'.getD x 0 < (chain cs x).length ∧
      deps h cs H' x = 0 := by
    intro x
    rw [hm x]
    constructor
    · rintro (rfl | hxf)
      · exact ⟨hc, hcl, hx.deps_c⟩
      · obtain ⟨hxc, hxst, hxd⟩ := (hmem x).mp hxf
        obtain ⟨hxl, hxh, _⟩ := (hx.frontier_iff' x).mp hxst
        rw [hx.head_ne hxc] at hxh
        exact ⟨hxl, hxh, hxd hxl⟩
    · rintro ⟨hxl, hxh, hxd⟩
      by_cases hxc : x = c
      · exact Or.inl hxc
      · right
        refine (hmem x).mpr ⟨hxc, (hx.frontier_iff' x).mpr ⟨hxl, by rw [hx.head_ne hxc]; exact hxh, ?_⟩,
          fun _ => hxd⟩
        have := hx.deps_ne hxc
        omega
  have hcand : CandList h cs (Before h cs) (ids fs) (frOf cs { stc with frontier := fr' }) := by
    refine ⟨hp, fun y => ?_⟩
    rw [hx.cand_iff']
    unfold frOf
    simp only [List.mem_map]
    constructor
    · rintro ⟨x, hxf, rfl⟩
      obtain ⟨hxl, hxh, hxd⟩ := (hmem' x).mp hxf
      exact ⟨x, hxl, hxh, by unfold hdOp; rw [hhead], hxd⟩
    · rintro ⟨d, hdl, hdh, rfl, hdd⟩
      exact ⟨d, (hmem' d).mpr ⟨hdl, hdh, hdd⟩, by unfold hdOp; rw [hhead]⟩
  refine ⟨⟨?_, by simp only; rw [hh, hH'], by simp only; rw [hh]; exact hpos,
    by simp only; rw [hh]; exact hHo, hx.below.2, framesStruct_lt hfs.1, ?_, ?_, ?_, ?_, hcand⟩,
    candList_unique hcand hfs.2.1 (fun _ => Iff.rfl)⟩
  · exact hx.shape (stc := { stc with frontier := fr' }) hh hv hf hn
  · intro c' k hk d hd hdc
    unfold ChSt.visAt at hk
    unfold ChSt.fuAt
    simp only at hk ⊢
    rw [hv] at hk; rw [hf]
    exact hfu c' k hk d hd hdc
  · intro c' k hk hkh
    unfold ChSt.visAt
    simp only
    rw [hv]
    refine hvis c' k hk (Nat.le_trans hkh ?_)
    rw [hhead]
    by_cases hcc : c' = c
    · subst hcc; rw [hx.head_c]; omega
    · rw [hx.head_ne hcc]; exact Nat.le_refl _
  · intro d hdl hdh
    rw [hhead] at hdh
    simp only
    rw [hh]
    by_cases hdc : d = c
    · subst hdc; rw [hnc, hx.deps_c]; rfl
    · exact hlo d hdc hdl hdl hdh
  · intro x hxf
    obtain ⟨hxl, hxh, _⟩ := (hmem' x).mp hxf
    exact ⟨hxl, by rw [hhead]; exact hxh⟩

end ctx

end unlift

end github_com.anishathalye.porcupine
end Perennial
