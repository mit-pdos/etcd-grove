/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/Replay.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: the **abstract replay** behind F1 (`lin_replay`; `notes/stage2-proof.md` §L, the
frontier step; `notes/unit-Lc.md`).

A list `Lf` of operations sorted by (place, rank), each with a place `pl a`, a rank (0: producer,
1: read), an input and an output, and a valuation `val` of tags. If
* producers are above `tag0`, everything is at least `tag0` and at most `F`;
* two producers at the same place are both writes;
* a write's place has its value; a read's place is `tag0` or a producer's place and the read
  returns the place's value; a CAS's place is the CAS of the value of a tag `t0` (`tag0` or a
  producer's place) just below it (no tag in between);
* `F` is `tag0` or a producer's place, `val tag0 = 0`,
then replaying `Lf`'s inputs from 0 gives the outputs and ends at `val F`.
-/
module

public import Dsverify.Proof.gryff.Pure.LinDefs
public import Dsverify.Proof.gryff.Proto.TagOrder

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.pureLc

open proto dsverify_lab.harness

section
variable {α : Type} (pl : α → PTag) (rk : α → Nat)

/-- The sort order of `Lf`: by place, then rank. -/
def SortRel (a b : α) : Prop := tagLt (pl a) (pl b) ∨ (pl a = pl b ∧ rk a ≤ rk b)

/-- `t` is `tag0` or a producer's place in `Lf`. -/
def IsP (Lf : List α) (t : PTag) : Prop := t = tag0 ∨ ∃ p ∈ Lf, rk p = 0 ∧ pl p = t

def IsWr (inp : α → RegInput w64) (a : α) : Prop := ∃ v, inp a = .write v

/-- The hypotheses of the abstract replay. -/
structure RH (inp : α → RegInput w64) (out : α → RegOutput w64) (val : PTag → w64) (F : PTag)
    (Lf : List α) : Prop where
  rank : ∀ a ∈ Lf, (rk a = 0 ∧ inp a ≠ .read) ∨ (rk a = 1 ∧ inp a = .read)
  sort : Lf.Pairwise (SortRel pl rk)
  uniq : Lf.Pairwise fun a b => rk a = 0 → rk b = 0 → pl a = pl b → IsWr inp a ∧ IsWr inp b
  ge0 : ∀ a ∈ Lf, tagLe tag0 (pl a)
  pos : ∀ a ∈ Lf, rk a = 0 → tagLt tag0 (pl a)
  read : ∀ a ∈ Lf, inp a = .read → IsP pl rk Lf (pl a) ∧ out a = .value (val (pl a))
  write : ∀ a ∈ Lf, ∀ v, inp a = .write v → val (pl a) = v ∧ out a = .done
  cas : ∀ a ∈ Lf, ∀ x y, inp a = .cas x y → out a = .done ∧ ∃ t0, IsP pl rk Lf t0 ∧
    tagLt t0 (pl a) ∧ (∀ z, tagLt t0 z → tagLt z (pl a) → False) ∧
    val (pl a) = (if val t0 = x then y else val t0)
  val0 : val tag0 = 0
  front : IsP pl rk Lf F
  le : ∀ a ∈ Lf, tagLe (pl a) F
  ge0F : tagLe tag0 F

variable {pl rk}

theorem RH.isP_ge0 {inp : α → RegInput w64} {out : α → RegOutput w64} {val : PTag → w64} {F : PTag}
    {Lf : List α} (H : RH pl rk inp out val F Lf) {t : PTag} (h : IsP pl rk Lf t) :
    tagLe tag0 t := by
  rcases h with rfl | ⟨p, hp, h0, rfl⟩
  · exact tagLe_refl _
  · exact tagLe_of_lt (H.pos p hp h0)

theorem RH.isP_le {inp : α → RegInput w64} {out : α → RegOutput w64} {val : PTag → w64} {F : PTag}
    {Lf : List α} (H : RH pl rk inp out val F Lf) {t : PTag} (h : IsP pl rk Lf t) :
    tagLe t F := by
  rcases h with rfl | ⟨p, hp, _, rfl⟩
  · exact H.ge0F
  · exact H.le p hp

theorem replay_gen {inp : α → RegInput w64} {out : α → RegOutput w64} {val : PTag → w64}
    {F : PTag} {Lf : List α} (H : RH pl rk inp out val F Lf) :
    ∀ (L P : List α), Lf = P ++ L → ∀ c, IsP pl rk Lf c →
      (∀ p ∈ P, rk p = 0 → tagLe (pl p) c) → (∀ a ∈ L, tagLe c (pl a)) →
      (∀ a ∈ L, rk a = 0 → pl a = c → IsWr inp a) →
      replayOk (val c) (L.map fun a => (inp a, out a)) (val F) := by
  intro L
  induction L with
  | nil =>
    intro P hP c hc hPc _ _
    simp only [List.map_nil, replayOk]
    rw [List.append_nil] at hP; subst hP
    have hFc : F = c := by
      apply tagLe_antisymm _ (H.isP_le hc)
      rcases H.front with hF | ⟨p, hp, h0, rfl⟩
      · rw [hF]; exact H.isP_ge0 hc
      · exact hPc p hp h0
    rw [hFc]
  | cons o L ih =>
    intro P hP c hc hPc hLc hLw
    have hoLf : o ∈ Lf := by rw [hP]; simp
    have hLf : ∀ a ∈ L, a ∈ Lf := fun a ha => by rw [hP]; simp [ha]
    have hpw : (o :: L).Pairwise (SortRel pl rk) := by
      have := H.sort; rw [hP] at this; exact (List.pairwise_append.1 this).2.1
    have huw : (o :: L).Pairwise fun a b => rk a = 0 → rk b = 0 → pl a = pl b →
        IsWr inp a ∧ IsWr inp b := by
      have := H.uniq; rw [hP] at this; exact (List.pairwise_append.1 this).2.1
    rw [List.pairwise_cons] at hpw huw
    have hP' : Lf = (P ++ [o]) ++ L := by rw [hP]; simp
    have hco : tagLe c (pl o) := hLc o (by simp)
    -- the tail sorts after `o`
    have hLo : ∀ a ∈ L, tagLe (pl o) (pl a) := fun a ha => by
      rcases hpw.1 a ha with h | ⟨h, _⟩
      · exact tagLe_of_lt h
      · rw [h]; exact tagLe_refl _
    simp only [List.map_cons, replayOk]
    rcases H.rank o hoLf with ⟨hr0, hinp⟩ | ⟨hr1, hinp⟩
    · -- a producer: `c < pl o`
      cases hi : inp o with
      | read => exact absurd hi hinp
      | write v =>
        obtain ⟨hv, hout⟩ := H.write o hoLf v hi
        refine ⟨by simp [casApply, hout], ?_⟩
        simp only [casApply]
        rw [← hv]
        refine ih (P ++ [o]) hP' (pl o) (Or.inr ⟨o, hoLf, hr0, rfl⟩) ?_ hLo ?_
        · intro p hp h0
          rcases List.mem_append.1 hp with hp | hp
          · exact tagLe_trans (hPc p hp h0) hco
          · rw [List.mem_singleton.1 hp]; exact tagLe_refl _
        · intro a ha h0 he
          exact (huw.1 a ha hr0 h0 he.symm).2
      | cas x y =>
        obtain ⟨hout, t0, ht0, hlt, hnb, hv⟩ := H.cas o hoLf x y hi
        -- `c` is `t0`
        have hcne : c ≠ pl o := by
          intro he
          obtain ⟨w, hw⟩ := hLw o (by simp) hr0 he.symm
          rw [hi] at hw; cases hw
        have hclt : tagLt c (pl o) := by
          rcases hco with h | h
          · exact h
          · exact absurd h hcne
        have hct : c = t0 := by
          rcases tagLt_or_le c t0 with h | h
          · exfalso
            rcases ht0 with rfl | ⟨p, hp, h0, rfl⟩
            · exact (not_tagLt_iff _ _).2 (H.isP_ge0 hc) h
            · rw [hP] at hp
              rcases List.mem_append.1 hp with hp | hp
              · exact (not_tagLt_iff _ _).2 (hPc p hp h0) h
              · rcases List.mem_cons.1 hp with rfl | hp
                · exact tagLt_irrefl _ hlt
                · exact (not_tagLt_iff _ _).2 (hLo p hp) hlt
          · rcases h with h | h
            · exfalso
              rcases hc with rfl | ⟨p, hp, h0, rfl⟩
              · exact (not_tagLt_iff _ _).2 (H.isP_ge0 ht0) h
              · exact hnb _ h hclt
            · exact h.symm
        subst hct
        refine ⟨by simp [casApply, hout], ?_⟩
        simp only [casApply]
        have hv' : (if val c = x then y else val c) = val (pl o) := by
          rw [hv]
        rw [hv']
        refine ih (P ++ [o]) hP' (pl o) (Or.inr ⟨o, hoLf, hr0, rfl⟩) ?_ hLo ?_
        · intro p hp h0
          rcases List.mem_append.1 hp with hp | hp
          · exact tagLe_trans (hPc p hp h0) hco
          · rw [List.mem_singleton.1 hp]; exact tagLe_refl _
        · intro a ha h0 he
          obtain ⟨w, hw⟩ := (huw.1 a ha hr0 h0 he.symm).1
          rw [hi] at hw; cases hw
    · -- a read: its place is `c`
      obtain ⟨hp, hout⟩ := H.read o hoLf hinp
      have hoc : pl o = c := by
        apply tagLe_antisymm _ hco
        rcases hp with h | ⟨p, hp, h0, hpe⟩
        · rw [h]; exact H.isP_ge0 hc
        · rw [hP] at hp
          rcases List.mem_append.1 hp with hp | hp
          · rw [← hpe]; exact hPc p hp h0
          · rcases List.mem_cons.1 hp with rfl | hp
            · omega
            · exfalso
              rcases hpw.1 p hp with h | ⟨_, h⟩
              · rw [hpe] at h; exact tagLt_irrefl _ h
              · omega
      rw [hinp]
      refine ⟨by simp [casApply, hout, hoc], ?_⟩
      simp only [casApply]
      refine ih (P ++ [o]) hP' c hc ?_ (fun a ha => hoc ▸ hLo a ha)
        (fun a ha h0 he => hLw a (by simp [ha]) h0 he)
      intro p hp h0
      rcases List.mem_append.1 hp with hp | hp
      · exact hPc p hp h0
      · rw [List.mem_singleton.1 hp] at h0; omega

/-- **The abstract replay.** -/
theorem replay {inp : α → RegInput w64} {out : α → RegOutput w64} {val : PTag → w64}
    {F : PTag} {Lf : List α} (H : RH pl rk inp out val F Lf) :
    replayOk 0 (Lf.map fun a => (inp a, out a)) (val F) := by
  have := replay_gen H Lf [] (by simp) tag0 (Or.inl rfl) (by simp) (fun a ha => H.ge0 a ha)
    (fun a ha h0 he => absurd he (tagLt_ne (H.pos a ha h0)).symm)
  rwa [H.val0] at this
end

end Perennial.gryff.pure.pureLc
