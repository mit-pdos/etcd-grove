/- Lean-first (no Rocq counterpart).

# Pure lemmas of `chains.lift` (2026-11-02)

`chains.lift` lifted client `i`'s head `y` (a candidate of `B = ids fs`, at position `idx` of
the frontier): the heads become `H' = H.set i (H[i] + 1)` (`LiftCtx`), the head of `i` is
visited (`computeFirstUnk`, `LiftCtx2`), its `nDeps` recounted (`cnt`, `cnt_succ`), the frontier
loses `i` and gets it back if it has no dependency, and the loop over `j` (`LiftInv`) decrements
the `nDeps` of the clients whose head's `FUe` on `i` was the new head of `i` (`deps_lift`),
adding those that reach `0`. At the end the chains' invariant holds at `y :: B`
(`LiftCtx2.inv_final`).
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.DagLemmas

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial
namespace github_com.anishathalye.porcupine

open Theory

variable {α : Type} {h : List (Op α)} {cs : List (List Nat)}

/-- What `nDeps[i]`'s recount has counted after the clients below `k`. -/
def cnt (h : List (Op α)) (cs : List (List Nat)) (H : List Nat) (c k : Nat) : Nat :=
  ((List.range k).filter
    (fun d => decide (d ≠ c ∧ H.getD c 0 < (chain cs c).length ∧
      H.getD d 0 < FUe h cs c d (H.getD c 0)))).length

theorem cnt_succ {H : List Nat} {c k : Nat} :
    cnt h cs H c (k + 1) = cnt h cs H c k +
      (if k ≠ c ∧ H.getD c 0 < (chain cs c).length ∧ H.getD k 0 < FUe h cs c k (H.getD c 0)
       then 1 else 0) := by
  unfold cnt
  rw [List.range_succ, List.filter_append, List.length_append]
  congr 1
  by_cases hp : k ≠ c ∧ H.getD c 0 < (chain cs c).length ∧ H.getD k 0 < FUe h cs c k (H.getD c 0)
  · rw [List.filter_cons, List.filter_nil, if_pos (decide_eq_true hp), if_pos hp]; rfl
  · rw [List.filter_cons, List.filter_nil, if_neg (by simpa using hp), if_neg hp]; rfl

theorem cnt_zero {H : List Nat} {c : Nat} : cnt h cs H c 0 = 0 := by simp [cnt]

theorem cnt_deps {H : List Nat} {c : Nat} : cnt h cs H c cs.length = deps h cs H c := rfl

theorem cnt_le {H : List Nat} {c k : Nat} : cnt h cs H c k ≤ k := by
  unfold cnt; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- `chains.lift`'s situation: client `i` is in the frontier, its head is `y`. -/
def LiftCtx (h : List (Op α)) (cs : List (List Nat)) (st : ChSt) (B : List Nat) (i y : Nat) :
    Prop :=
  ChainsOk h cs ∧ CallLeRet h ∧ ChainsInv h cs B st ∧ i < cs.length ∧
  st.head i < (chain cs i).length ∧ hdOp cs st i = y ∧ i ∈ st.frontier

section ctx
variable {st : ChSt} {B : List Nat} {i y : Nat}

/-- The heads after lifting. -/
def LiftCtx.H' (_ : LiftCtx h cs st B i y) : List Nat := st.heads.set i (st.head i + 1)

theorem LiftCtx.heads_length (hx : LiftCtx h cs st B i y) : st.heads.length = cs.length :=
  hx.2.2.1.1.1

theorem LiftCtx.H'_getD (hx : LiftCtx h cs st B i y) (d : Nat) :
    (st.heads.set i (st.head i + 1)).getD d 0 = if d = i then st.head i + 1 else st.head d := by
  rw [set_getD (by rw [hx.heads_length]; exact hx.2.2.2.1)]; rfl

theorem LiftCtx.cand (hx : LiftCtx h cs st B i y) : Cand h (Before h cs) B y := by
  obtain ⟨_, _, hci, _, _, hop, hfr⟩ := hx
  refine (hci.2.2.2.2.2.2.2.2.2.2.2 y).mp ?_
  rw [← hop]; exact List.mem_map_of_mem hfr

theorem LiftCtx.yget (hx : LiftCtx h cs st B i y) : (chain cs i)[st.head i]? = some y := by
  rw [← hx.2.2.2.2.2.1]; exact opAt_get hx.2.2.2.2.1

theorem LiftCtx.ylt (hx : LiftCtx h cs st B i y) : y < h.length :=
  lt_length_of_mem hx.1 (List.mem_of_getElem? hx.yget)

theorem LiftCtx.clientOf (hx : LiftCtx h cs st B i y) : clientOf cs y = i :=
  clientOf_eq hx.1 hx.2.2.2.1 (List.mem_of_getElem? hx.yget)

/-- The operations `y :: B`, at the heads `H'`. -/
theorem LiftCtx.push (hx : LiftCtx h cs st B i y) :
    PosOk cs (y :: B) (st.heads.set i (st.head i + 1)) ∧
      HeadsOk cs (st.heads.set i (st.head i + 1)) := by
  obtain ⟨hok, hwf, hci, hi, hil, hop, hfr⟩ := hx
  have hx : LiftCtx h cs st B i y := ⟨hok, hwf, hci, hi, hil, hop, hfr⟩
  obtain ⟨_, hheads, hpos, hH, hclos, hlt, _⟩ := hci
  obtain ⟨c, _, hcl, hcop, hpos', hH'⟩ := posOk_push hok hwf hpos hH hlt hclos hx.cand
  have : c = i := (pos_unique hok (by rw [← hcop]; exact opAt_get hcl) hx.yget).1
  subst this
  exact ⟨hpos', hH'⟩

theorem LiftCtx.closed (hx : LiftCtx h cs st B i y) :
    ∀ z w, w ∈ y :: B → Before h cs z w → z ∈ y :: B := by
  intro z w hw hzw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact List.mem_cons_of_mem _ (hx.cand.2.2 z hzw)
  · exact List.mem_cons_of_mem _ (hx.2.2.1.2.2.2.2.1 z w hw hzw)

theorem LiftCtx.cand' (hx : LiftCtx h cs st B i y) (z : Nat) :
    Cand h (Before h cs) (y :: B) z ↔ ∃ d, d < cs.length ∧
      (st.heads.set i (st.head i + 1)).getD d 0 < (chain cs d).length ∧
      opAt cs d ((st.heads.set i (st.head i + 1)).getD d 0) = z ∧
      deps h cs (st.heads.set i (st.head i + 1)) d = 0 := by
  have hlt : ∀ x ∈ y :: B, x < h.length := by
    intro x hx'; rcases List.mem_cons.mp hx' with rfl | hx'
    · exact hx.ylt
    · exact hx.2.2.1.2.2.2.2.2.1 x hx'
  exact cand_iff hx.1 hx.2.1 (ids_iff_headsSet hx.1 hx.push.1 hlt) hx.closed

/-- `deps_lift`. -/
theorem LiftCtx.deps_ne (hx : LiftCtx h cs st B i y) {d : Nat} (hd : d ≠ i) :
    deps h cs st.heads d = deps h cs (st.heads.set i (st.head i + 1)) d +
      (if st.head d < (chain cs d).length ∧ FUe h cs d i (st.head d) = st.head i + 1
       then 1 else 0) :=
  deps_lift hd (by rw [hx.heads_length]; exact hx.2.2.2.1)

theorem LiftCtx.frontier_iff' (hx : LiftCtx h cs st B i y) (x : Nat) :
    x ∈ st.frontier ↔ x < cs.length ∧ st.head x < (chain cs x).length ∧
      deps h cs st.heads x = 0 :=
  frontier_iff hx.1 hx.2.1 hx.2.2.1 x

/-- A client other than `i` without dependency at the new heads is a candidate of `y :: B`. -/
theorem LiftCtx.cand_of (hx : LiftCtx h cs st B i y) {d : Nat} (hdl : d < cs.length)
    (hdh : (st.heads.set i (st.head i + 1)).getD d 0 < (chain cs d).length)
    (hdd : deps h cs (st.heads.set i (st.head i + 1)) d = 0) :
    Cand h (Before h cs) (y :: B) (opAt cs d ((st.heads.set i (st.head i + 1)).getD d 0)) :=
  (hx.cand' _).mpr ⟨d, hdl, hdh, rfl, hdd⟩

end ctx

/-- After `computeFirstUnk(i)`: the state `st2` (heads `H'`, the head of `i` visited). -/
def LiftCtx2 (h : List (Op α)) (cs : List (List Nat)) (st st2 : ChSt) (B : List Nat) (i y : Nat) :
    Prop :=
  LiftCtx h cs st B i y ∧ st2.heads = st.heads.set i (st.head i + 1) ∧ st2.nDeps = st.nDeps ∧
  ShapeOk cs st2 ∧ FuOk h cs st2 ∧
  ∀ c' k, st2.visAt c' k = (st.visAt c' k ||
    decide (c' = i ∧ k = (st.heads.set i (st.head i + 1)).getD c' 0 ∧ k < (chain cs c').length))

/-- The `j`-loop's invariant (clients below `j` processed). -/
def LiftInv (h : List (Op α)) (cs : List (List Nat)) (st st2 : ChSt) (i j : Nat) (stc : ChSt) :
    Prop :=
  stc.heads = st2.heads ∧ stc.vis = st2.vis ∧ stc.fu = st2.fu ∧
  stc.nDeps.length = st.nDeps.length ∧
  (st2.head i < (chain cs i).length → sint.Z (stc.nDeps.getD i 0) = deps h cs st2.heads i) ∧
  (∀ d, d ≠ i → d < j → d < cs.length → st2.head d < (chain cs d).length →
    sint.Z (stc.nDeps.getD d 0) = deps h cs st2.heads d) ∧
  (∀ d, d ≠ i → j ≤ d → stc.nDeps.getD d 0 = st.nDeps.getD d 0) ∧
  (frOf cs stc).Pairwise (KeyGt h cs) ∧
  (∀ x, x ∈ stc.frontier ↔ x < cs.length ∧ st2.head x < (chain cs x).length ∧
    deps h cs st2.heads x = 0 ∧ (x = i ∨ x < j ∨ x ∈ st.frontier))

section ctx2
variable {st st2 : ChSt} {B : List Nat} {i y : Nat}

theorem LiftCtx2.head2 (hx : LiftCtx2 h cs st st2 B i y) (d : Nat) :
    st2.head d = if d = i then st.head i + 1 else st.head d := by
  unfold ChSt.head; rw [hx.2.1, hx.1.H'_getD]; rfl

theorem LiftCtx2.head2_ne (hx : LiftCtx2 h cs st st2 B i y) {d : Nat} (hd : d ≠ i) :
    st2.head d = st.head d := by rw [hx.head2, if_neg hd]

theorem LiftCtx2.head2_i (hx : LiftCtx2 h cs st st2 B i y) : st2.head i = st.head i + 1 := by
  rw [hx.head2, if_pos rfl]

theorem LiftCtx2.cand2 (hx : LiftCtx2 h cs st st2 B i y) (z : Nat) :
    Cand h (Before h cs) (y :: B) z ↔ ∃ d, d < cs.length ∧ st2.head d < (chain cs d).length ∧
      opAt cs d (st2.head d) = z ∧ deps h cs st2.heads d = 0 := by
  rw [hx.1.cand' z]
  simp only [ChSt.head, hx.2.1]

theorem LiftCtx2.deps2_ne (hx : LiftCtx2 h cs st st2 B i y) {d : Nat} (hd : d ≠ i) :
    deps h cs st.heads d = deps h cs st2.heads d +
      (if st2.head d < (chain cs d).length ∧ FUe h cs d i (st2.head d) = st2.head i
       then 1 else 0) := by
  rw [hx.1.deps_ne hd, hx.2.1, hx.head2_ne hd, hx.head2_i]

theorem LiftCtx2.hdOp_ne (hx : LiftCtx2 h cs st st2 B i y) {stc : ChSt}
    (hh : stc.heads = st2.heads) {d : Nat} (hd : d ≠ i) : hdOp cs stc d = hdOp cs st d := by
  unfold hdOp
  rw [show stc.head d = st2.head d by unfold ChSt.head; rw [hh], hx.head2_ne hd]

/-- A frontier member at the new heads is a candidate of `y :: B`. -/
theorem LiftCtx2.member_cand (hx : LiftCtx2 h cs st st2 B i y) {stc : ChSt}
    (hh : stc.heads = st2.heads) {x : Nat} (hxl : x < cs.length)
    (hxh : st2.head x < (chain cs x).length) (hxd : deps h cs st2.heads x = 0) :
    Cand h (Before h cs) (y :: B) (hdOp cs stc x) := by
  refine (hx.cand2 _).mpr ⟨x, hxl, hxh, ?_, hxd⟩
  unfold hdOp; unfold ChSt.head; rw [hh]

/-- `addToFrontier(x)`'s premises: a candidate client added to a frontier of candidates. -/
theorem LiftCtx2.add_pre (hx : LiftCtx2 h cs st st2 B i y) {stc : ChSt}
    (hh : stc.heads = st2.heads) {x : Nat} (hxl : x < cs.length)
    (hxh : st2.head x < (chain cs x).length) (hxd : deps h cs st2.heads x = 0)
    (hmem : ∀ v ∈ stc.frontier, v < cs.length ∧ st2.head v < (chain cs v).length ∧
      deps h cs st2.heads v = 0) :
    stc.head x < (chain cs x).length ∧
    ∀ v ∈ stc.frontier, v < cs.length ∧ stc.head v < (chain cs v).length ∧
      ¬ Prec h (hdOp cs stc x) (hdOp cs stc v) ∧ ¬ Prec h (hdOp cs stc v) (hdOp cs stc x) := by
  have hst : ∀ d, stc.head d = st2.head d := fun d => by unfold ChSt.head; rw [hh]
  have hcx := hx.member_cand hh hxl hxh hxd
  refine ⟨by rw [hst]; exact hxh, fun v hv => ?_⟩
  obtain ⟨hvl, hvh, hvd⟩ := hmem v hv
  have hcv := hx.member_cand hh hvl hvh hvd
  exact ⟨hvl, by rw [hst]; exact hvh, fun hp => cand_not_prec hcx hcv (Or.inl hp),
    fun hp => cand_not_prec hcv hcx (Or.inl hp)⟩

theorem LiftInv.members (hi : LiftInv h cs st st2 i j stc) :
    ∀ v ∈ stc.frontier, v < cs.length ∧ st2.head v < (chain cs v).length ∧
      deps h cs st2.heads v = 0 := by
  intro v hv
  obtain ⟨a, b, c, _⟩ := (hi.2.2.2.2.2.2.2.2 v).mp hv
  exact ⟨a, b, c⟩

/-- The loop's start, `i` not re-added (it is finished or has a dependency). -/
theorem LiftCtx2.inv_init_erase (hx : LiftCtx2 h cs st st2 B i y) {stc : ChSt}
    (hh : stc.heads = st2.heads) (hv : stc.vis = st2.vis) (hf : stc.fu = st2.fu)
    (hn : stc.nDeps.length = st.nDeps.length)
    (hni : st2.head i < (chain cs i).length → sint.Z (stc.nDeps.getD i 0) = deps h cs st2.heads i)
    (hno : ∀ d, d ≠ i → stc.nDeps.getD d 0 = st.nDeps.getD d 0)
    (hfr : stc.frontier = st.frontier.erase i)
    (hnot : ¬ (st2.head i < (chain cs i).length ∧ deps h cs st2.heads i = 0)) :
    LiftInv h cs st st2 i 0 stc := by
  have hci := hx.1.2.2.1
  have hnd : st.frontier.Nodup := nodup_of_sorted hci.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hh, hv, hf, hn, hni, fun d _ hd => absurd hd (Nat.not_lt_zero _),
    fun d hd _ => hno d hd, ?_, fun x => ?_⟩
  · have heq : frOf cs stc = (st.frontier.erase i).map (hdOp cs st) := by
      unfold frOf; rw [hfr]
      refine List.map_congr_left fun v hv' => hx.hdOp_ne hh ?_
      exact (hnd.mem_erase_iff.mp hv').1
    rw [heq]
    exact hci.2.2.2.2.2.2.2.2.2.2.1.sublist (List.erase_sublist.map _)
  · rw [hfr, hnd.mem_erase_iff]
    constructor
    · rintro ⟨hxi, hxf⟩
      obtain ⟨hxl, hxh, hxd⟩ := (hx.1.frontier_iff' x).mp hxf
      have := hx.deps2_ne hxi
      exact ⟨hxl, by rw [hx.head2_ne hxi]; exact hxh, by omega, Or.inr (Or.inr hxf)⟩
    · rintro ⟨hxl, hxh, hxd, hxo⟩
      rcases hxo with rfl | hxo | hxf
      · exact absurd ⟨hxh, hxd⟩ hnot
      · exact absurd hxo (Nat.not_lt_zero _)
      · exact ⟨fun he => hnot (he ▸ ⟨hxh, hxd⟩), hxf⟩

/-- The loop's start, `i` re-added (`addToFrontier(i)`'s post). -/
theorem LiftCtx2.inv_init_add (hx : LiftCtx2 h cs st st2 B i y) {stc : ChSt}
    (hh : stc.heads = st2.heads) (hv : stc.vis = st2.vis) (hf : stc.fu = st2.fu)
    (hn : stc.nDeps.length = st.nDeps.length)
    (hni : sint.Z (stc.nDeps.getD i 0) = deps h cs st2.heads i)
    (hno : ∀ d, d ≠ i → stc.nDeps.getD d 0 = st.nDeps.getD d 0)
    (hp : (frOf cs stc).Pairwise (KeyGt h cs))
    (hfr : ∀ x, x ∈ stc.frontier ↔ x = i ∨ x ∈ st.frontier.erase i)
    (hyes : st2.head i < (chain cs i).length ∧ deps h cs st2.heads i = 0) :
    LiftInv h cs st st2 i 0 stc := by
  have hci := hx.1.2.2.1
  have hnd : st.frontier.Nodup := nodup_of_sorted hci.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hh, hv, hf, hn, fun _ => hni, fun d _ hd => absurd hd (Nat.not_lt_zero _),
    fun d hd _ => hno d hd, hp, fun x => ?_⟩
  rw [hfr, hnd.mem_erase_iff]
  constructor
  · rintro (rfl | ⟨hxi, hxf⟩)
    · exact ⟨hx.1.2.2.2.1, hyes.1, hyes.2, Or.inl rfl⟩
    · obtain ⟨hxl, hxh, hxd⟩ := (hx.1.frontier_iff' x).mp hxf
      have := hx.deps2_ne hxi
      exact ⟨hxl, by rw [hx.head2_ne hxi]; exact hxh, by omega, Or.inr (Or.inr hxf)⟩
  · rintro ⟨hxl, hxh, hxd, hxo⟩
    by_cases hxi : x = i
    · exact Or.inl hxi
    · rcases hxo with hxo | hxo | hxf
      · exact absurd hxo hxi
      · exact absurd hxo (Nat.not_lt_zero _)
      · exact Or.inr ⟨hxi, hxf⟩

/-- The `j`-loop, nothing to do at `j`. -/
theorem LiftCtx2.inv_skip (hx : LiftCtx2 h cs st st2 B i y) {j : Nat} {stc : ChSt}
    (hi : LiftInv h cs st st2 i j stc)
    (hcond : j = i ∨ ¬ st2.head j < (chain cs j).length ∨
      FUe h cs j i (st2.head j) ≠ st2.head i) :
    LiftInv h cs st st2 i (j + 1) stc := by
  obtain ⟨hh, hv, hf, hn, hni, hlo, hhi, hp, hmem⟩ := hi
  have hnoh : ∀ d, d ≠ i → st2.head d < (chain cs d).length → d = j →
      deps h cs st.heads d = deps h cs st2.heads d := by
    rintro d hdi hdh rfl
    rw [hx.deps2_ne hdi]
    have : ¬ (st2.head d < (chain cs d).length ∧ FUe h cs d i (st2.head d) = st2.head i) := by
      rintro ⟨h1, h2⟩
      rcases hcond with h0 | h0 | h0
      · exact hdi h0
      · exact h0 h1
      · exact h0 h2
    rw [if_neg this, Nat.add_zero]
  refine ⟨hh, hv, hf, hn, hni, fun d hdi hd hdl hdh => ?_, fun d hdi hd => hhi d hdi (by omega),
    hp, fun x => ?_⟩
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
    · exact hlo d hdi hd hdl hdh
    · rw [hhi d hdi (Nat.le_refl _), ← hnoh d hdi hdh rfl]
      exact hx.1.2.2.1.2.2.2.2.2.2.2.2.1 d hdl (by rw [← hx.head2_ne hdi]; exact hdh)
  · rw [hmem x]
    constructor
    · rintro ⟨a, b, c, d⟩
      refine ⟨a, b, c, ?_⟩
      rcases d with d | d | d
      · exact Or.inl d
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr d)
    · rintro ⟨a, b, c, d⟩
      refine ⟨a, b, c, ?_⟩
      rcases d with d | d | d
      · exact Or.inl d
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ d) with d | rfl
        · exact Or.inr (Or.inl d)
        · by_cases hxi : x = i
          · exact Or.inl hxi
          · right; right
            refine (hx.1.frontier_iff' x).mpr ⟨a, by rw [← hx.head2_ne hxi]; exact b, ?_⟩
            rw [hnoh x hxi b rfl, c]
      · exact Or.inr (Or.inr d)

/-- The `j`-loop, `nDeps[j]` decremented (and `j` added if it reached `0`: `hfr'`). -/
theorem LiftCtx2.inv_hit (hx : LiftCtx2 h cs st st2 B i y) {j : Nat} {stc stc' : ChSt}
    (hi : LiftInv h cs st st2 i j stc) (hji : j ≠ i) (hjl : j < cs.length)
    (hjh : st2.head j < (chain cs j).length) (hfu : FUe h cs j i (st2.head j) = st2.head i)
    (hcs : (cs.length : Int) < 2 ^ 62)
    (hh' : stc'.heads = stc.heads) (hv' : stc'.vis = stc.vis) (hf' : stc'.fu = stc.fu)
    (hn' : stc'.nDeps = stc.nDeps.set j (stc.nDeps.getD j 0 - W64 1))
    (hp' : (frOf cs stc').Pairwise (KeyGt h cs))
    (hfr' : ∀ x, x ∈ stc'.frontier ↔
      (x = j ∧ stc.nDeps.getD j 0 - W64 1 = W64 0) ∨ x ∈ stc.frontier) :
    LiftInv h cs st st2 i (j + 1) stc' := by
  obtain ⟨hh, hv, hf, hn, hni, hlo, hhi, hp, hmem⟩ := hi
  have hjn : j < stc.nDeps.length := by rw [hn, hx.1.2.2.1.1.2.1]; exact hjl
  have hold : stc.nDeps.getD j 0 = st.nDeps.getD j 0 := hhi j hji (Nat.le_refl _)
  have hz : sint.Z (stc.nDeps.getD j 0) = deps h cs st.heads j := by
    rw [hold]; exact hx.1.2.2.1.2.2.2.2.2.2.2.2.1 j hjl (by rw [← hx.head2_ne hji]; exact hjh)
  have hdj : deps h cs st.heads j = deps h cs st2.heads j + 1 := by
    rw [hx.deps2_ne hji, if_pos ⟨hjh, hfu⟩]
  have hdle : deps h cs st.heads j ≤ cs.length := deps_le
  have hdec : sint.Z (stc.nDeps.getD j 0 - W64 1) = deps h cs st2.heads j := by
    have h2 : (deps h cs st.heads j : Int) ≤ cs.length := by exact_mod_cast hdle
    have h1 := hz
    have : sint.Z (stc.nDeps.getD j 0 - W64 1) = sint.Z (stc.nDeps.getD j 0) - 1 := by word
    rw [this, hz, hdj]; push_cast; omega
  have hget : ∀ d, stc'.nDeps.getD d 0 =
      if d = j then stc.nDeps.getD j 0 - W64 1 else stc.nDeps.getD d 0 := by
    intro d
    rw [hn']
    by_cases hdj' : d = j
    · subst hdj'; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hjn]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hdj'), hdj']
  have hjnot : j ∉ stc.frontier := by
    intro hjf
    obtain ⟨_, _, _, hjo⟩ := (hmem j).mp hjf
    rcases hjo with h0 | h0 | h0
    · exact hji h0
    · exact Nat.lt_irrefl _ h0
    · obtain ⟨_, _, hd0⟩ := (hx.1.frontier_iff' j).mp h0
      omega
  refine ⟨by rw [hh', hh], by rw [hv', hv], by rw [hf', hf], by rw [hn', List.length_set, hn],
    fun hih => ?_, fun d hdi hd hdl hdh => ?_, fun d hdi hd => ?_, hp', fun x => ?_⟩
  · rw [hget i, if_neg (Ne.symm hji)]; exact hni hih
  · rw [hget d]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
    · rw [if_neg (show d ≠ j by omega)]; exact hlo d hdi hd hdl hdh
    · rw [if_pos rfl]; exact hdec
  · rw [hget d, if_neg (show d ≠ j by omega), hhi d hdi (by omega)]
  · rw [hfr' x, hmem x]
    constructor
    · rintro (⟨rfl, h0⟩ | ⟨a, b, c, d⟩)
      · refine ⟨hjl, hjh, ?_, Or.inr (Or.inl (by omega))⟩
        rw [h0] at hdec; simpa using hdec.symm
      · refine ⟨a, b, c, ?_⟩
        rcases d with d | d | d
        · exact Or.inl d
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr d)
    · rintro ⟨a, b, c, d⟩
      by_cases hxj : x = j
      · subst hxj
        left; refine ⟨rfl, ?_⟩
        rw [c] at hdec
        exact BitVec.eq_of_toInt_eq (by simpa using hdec)
      · right
        refine ⟨a, b, c, ?_⟩
        rcases d with d | d | d
        · exact Or.inl d
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr d)

/-- The loop's end: the chains' invariant at `y :: B`, and the frontier is its candidate list. -/
theorem LiftCtx2.inv_final (hx : LiftCtx2 h cs st st2 B i y) {stc : ChSt}
    (hi : LiftInv h cs st st2 i cs.length stc) :
    ChainsInv h cs (y :: B) stc ∧ CandList h cs (Before h cs) (y :: B) (frOf cs stc) := by
  obtain ⟨hx1, hh2, hn2, hsh2, hfu2, hvis2⟩ := hx
  have hx : LiftCtx2 h cs st st2 B i y := ⟨hx1, hh2, hn2, hsh2, hfu2, hvis2⟩
  obtain ⟨hh, hv, hf, hn, hni, hlo, hhi, hp, hmem⟩ := hi
  have hci := hx1.2.2.1
  have hst : ∀ d, stc.head d = st2.head d := fun d => by unfold ChSt.head; rw [hh]
  have hcand : CandList h cs (Before h cs) (y :: B) (frOf cs stc) := by
    refine ⟨hp, fun z => ?_⟩
    rw [hx.cand2]
    unfold frOf
    simp only [List.mem_map]
    constructor
    · rintro ⟨x, hxf, rfl⟩
      obtain ⟨hxl, hxh, hxd, _⟩ := (hmem x).mp hxf
      exact ⟨x, hxl, hxh, by unfold hdOp; rw [hst], hxd⟩
    · rintro ⟨d, hdl, hdh, rfl, hdd⟩
      exact ⟨d, (hmem d).mpr ⟨hdl, hdh, hdd, Or.inr (Or.inl hdl)⟩, by unfold hdOp; rw [hst]⟩
  have hlt : ∀ x ∈ y :: B, x < h.length := by
    intro x hx'; rcases List.mem_cons.mp hx' with rfl | hx'
    · exact hx1.ylt
    · exact hci.2.2.2.2.2.1 x hx'
  obtain ⟨hpos, hHo⟩ := hx1.push
  refine ⟨⟨?_, ?_, by rw [hh, hh2]; exact hpos, by rw [hh, hh2]; exact hHo, hx1.closed, hlt,
    ?_, ?_, ?_, ?_, hcand⟩, hcand⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hsh2
    refine ⟨by rw [hh]; exact h1, by rw [hn, hci.1.2.1], by rw [hv]; exact h3, by rw [hf]; exact h4, ?_⟩
    intro c' k hk
    unfold ChSt.fuAt
    rw [hv, hf]
    exact h5 c' k hk
  · rw [hh, hh2]
    exact headsOf_eq hpos hHo |>.symm
  · intro c' k hk d hd hdc
    unfold ChSt.visAt at hk
    unfold ChSt.fuAt
    rw [hv] at hk; rw [hf]
    exact hfu2 c' k hk d hd hdc
  · intro c' k hk hkh
    unfold ChSt.visAt
    rw [hv]
    have := hvis2 c' k
    unfold ChSt.visAt at this
    rw [this]
    rw [hst] at hkh
    by_cases hci' : c' = i
    · subst hci'
      rw [hx.head2_i] at hkh
      rcases Nat.lt_or_eq_of_le hkh with hkh | hkh
      · have := hci.2.2.2.2.2.2.2.1 c' k hk (by omega)
        unfold ChSt.visAt at this
        rw [this]
      · apply Bool.or_eq_true_iff.mpr; right; apply decide_eq_true
        refine ⟨rfl, ?_, hk⟩
        rw [hkh, hx1.H'_getD, if_pos rfl]
    · rw [hx.head2_ne hci'] at hkh
      have := hci.2.2.2.2.2.2.2.1 c' k hk hkh
      unfold ChSt.visAt at this
      rw [this]
  · intro d hdl hdh
    rw [hst] at hdh
    rw [hh]
    by_cases hdi : d = i
    · subst hdi; exact hni hdh
    · exact hlo d hdi hdl hdl hdh
  · intro x hxf
    obtain ⟨hxl, hxh, _⟩ := (hmem x).mp hxf
    exact ⟨hxl, by rw [hst]; exact hxh⟩

end ctx2

end github_com.anishathalye.porcupine
end Perennial
