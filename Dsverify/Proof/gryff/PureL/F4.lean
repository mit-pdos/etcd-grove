/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/F4.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: helpers for F4 (`ops`' indices, `opLe` a total preorder, `lin`'s filtered list).
-/
module

public import Dsverify.Proof.gryff.Pure.LinDefs
public import Dsverify.Proof.gryff.PureL.Sort

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-- The function `ops` maps over the run's indices. -/
noncomputable def opAt (l : List Label) (g : Nat) : Option Op :=
  match l[g]? with
  | some (r, e) => e.clientReq.map fun x =>
      { g, r, j := (projR (l.take g) r).length, cid := x.1, rid := x.2.1, inp := x.2.2 }
  | none => none

theorem ops_eq (l : List Label) : ops l = (List.range l.length).filterMap (opAt l) := rfl

theorem opAt_g {l : List Label} {g : Nat} {o : Op} (h : opAt l g = some o) : o.g = g := by
  unfold opAt at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; rfl
  · cases h

theorem mem_ops {l : List Label} {o : Op} : o ∈ ops l ↔ o.g < l.length ∧ opAt l o.g = some o := by
  rw [ops_eq, List.mem_filterMap]
  constructor
  · rintro ⟨g, hg, h⟩
    rw [opAt_g h]; exact ⟨List.mem_range.1 hg, h⟩
  · rintro ⟨h1, h2⟩; exact ⟨o.g, List.mem_range.2 h1, h2⟩

theorem ops_g_inj {l : List Label} {o o' : Op} (ho : o ∈ ops l) (ho' : o' ∈ ops l)
    (h : o.g = o'.g) : o = o' := by
  have a := (mem_ops.1 ho).2; have b := (mem_ops.1 ho').2
  rw [h, b] at a; exact Option.some.inj a.symm

theorem opAt_take {l : List Label} {k g : Nat} :
    opAt (l.take k) g = (opAt l g).filter fun o => decide (o.g < k) := by
  by_cases hg : g < k
  · have e1 : (l.take k)[g]? = l[g]? := by rw [List.getElem?_take]; simp [hg]
    have e2 : (l.take k).take g = l.take g := by rw [List.take_take]; congr 1; omega
    unfold opAt; rw [e1, e2]
    split
    · cases h : Option.map _ _ with
      | none => rfl
      | some o =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨_, _, rfl⟩ := h; simp [Option.filter, hg]
    · rfl
  · have e1 : (l.take k)[g]? = none := by rw [List.getElem?_take]; simp [hg]
    have : opAt (l.take k) g = none := by unfold opAt; rw [e1]
    rw [this]
    cases h : opAt l g with
    | none => rfl
    | some o => have := opAt_g h; simp [Option.filter, this, hg]

theorem ops_take (l : List Label) (k : Nat) :
    (ops l).filter (fun o => decide (o.g < k)) = ops (l.take k) := by
  rw [ops_eq, ops_eq, List.filter_filterMap]
  simp only [← opAt_take]
  apply pureL.filterMap_range_eq (by rw [List.length_take]; exact Nat.min_le_right _ _)
  intro g hg
  rw [opAt_take]
  cases h : opAt l g with
  | none => rfl
  | some o =>
    have := opAt_g h
    have hl : g < l.length := by
      unfold opAt at h; split at h
      · rename_i _ _ _ he; exact (List.getElem?_eq_some_iff.1 he).1
      · cases h
    simp at hg; simp; omega

theorem opLe_eq (l : List Label) (a b : Op) : opLe l a b =
    pureL.lexB (((place l a).map model.Tag.toP).getD proto.tag0)
      (((place l b).map model.Tag.toP).getD proto.tag0) a.rank b.rank a.g b.g := rfl

theorem opLe_total (l : List Label) (a b : Op) : opLe l a b || opLe l b a := by
  rw [opLe_eq, opLe_eq]; exact pureL.lexB_total ..

theorem opLe_trans (l : List Label) (a b c : Op) : opLe l a b → opLe l b c → opLe l a c := by
  rw [opLe_eq, opLe_eq, opLe_eq]; exact pureL.lexB_trans

theorem opLe_antisymm {l : List Label} {a b : Op} (ha : a ∈ ops l) (hb : b ∈ ops l)
    (h1 : opLe l a b) (h2 : opLe l b a) : a = b := by
  rw [opLe_eq] at h1 h2
  exact ops_g_inj ha hb (pureL.lexB_antisymm h1 h2)

theorem front_congr {l l' : List Label} {k : Nat} (hk : l.take k = l'.take k) :
    front l k = front l' k := by
  simp only [front, cutSt, hk]

theorem frontVal_congr {l l' : List Label} {k : Nat} (hk : l.take k = l'.take k) :
    frontVal l k = frontVal l' k := by
  unfold frontVal front cutSt; rw [hk]

/-- `lin`'s filtered list: the operations created within `k` whose place is below the frontier. -/
theorem lin_filter (l : List Label) (k : Nat) :
    (ops l).filter (fun o => decide (o.g < k) && placeLe l o (front l k)) =
      (ops (l.take k)).filter (fun o => placeLe l o (front l k)) := by
  rw [← ops_take, List.filter_filter]
  apply List.filter_congr; intro o _; rw [Bool.and_comm]

end Perennial.gryff.pure
