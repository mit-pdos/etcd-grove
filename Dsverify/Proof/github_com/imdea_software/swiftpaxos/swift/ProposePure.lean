/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ProposePure.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The pure facts `handlePropose`'s pre-acceptance (`swift.preaccept_dstep`) needs, from a
proposal's `propFacts` (round 14).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Steps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Local

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

theorem swift.before_snoc (t : sp.Seq) (y : sp.CmdId) (c : sp.Cmd) (h : y ∉ t.map Prod.fst) :
    sp.before (t ++ [(y, c)]) y = t ∧ sp.cmdIn (t ++ [(y, c)]) y = some c := by
  unfold sp.before sp.cmdIn
  induction t with
  | nil => simp
  | cons p t ih =>
    have hp : p.1 ≠ y := fun e => h (by simp [e])
    have h' : y ∉ t.map Prod.fst := fun hm => h (by simp at hm ⊢; exact Or.inr hm)
    obtain ⟨h1, h2⟩ := ih h'
    have hb : (p.1 != y) = true := by simpa using hp
    have hb' : (p.1 == y) = false := by simpa using hp
    simp only [List.cons_append, List.takeWhile_cons, hb, ite_true, List.find?_cons, hb']
    exact ⟨by rw [h1], h2⟩

theorem swift.takeWhile_ne_snoc (t : sp.Seq) (y : sp.CmdId) (c : sp.Cmd)
    (h : y ∉ t.map Prod.fst) : (t ++ [(y, c)]).takeWhile (·.1 != y) = t :=
  (swift.before_snoc t y c h).1

/-- The pre-acceptance's premises from a proposal's facts. -/
theorem swift.propFacts_pre (s : sp.Seq) (B D P : List sp.CmdId) (y : sp.CmdId) (c : sp.Cmd)
    (ld : Bool) (N r b : Nat)
    (h1 : s.getLast? = some (y, c)) (h2 : y ∉ (s.dropLast).map Prod.fst)
    (h3 : D = sp.lkDeps s.dropLast c) (h4 : P.getLast? = some y)
    (h5 : ld = true → P = swift.idsOfKey (s.dropLast.drop B.length) c.key ++ [y])
    (h6 : ∀ z ∈ swift.idsOfKey (s.dropLast.drop B.length) c.key, z ∈ P)
    (h7 : ld = true ↔ sp.leaderOf N b = r) (h8 : B <+: (s.dropLast).map Prod.fst) :
    y ∈ s.map Prod.fst ∧ D = sp.depsIn s y ∧ y ∉ B ∧
      (r = sp.leaderOf N b → P = sp.kpOf s B y) ∧ (∀ z ∈ sp.kpOf s B y, z ∈ P) := by
  have hs : s = s.dropLast ++ [(y, c)] := by
    have h1' := h1
    rw [List.getLast?_eq_some_iff] at h1'
    obtain ⟨t, rfl⟩ := h1'
    simp
  generalize ht : s.dropLast = t at *
  subst hs
  obtain ⟨hbef, hcmd⟩ := swift.before_snoc t y c h2
  have hBl : B.length ≤ t.length := by
    have := h8.length_le; simpa using this
  have hkp : sp.kpOf (t ++ [(y, c)]) B y = swift.idsOfKey (t.drop B.length) c.key ++ [y] := by
    unfold sp.kpOf
    rw [hcmd]
    simp only
    rw [List.drop_append_of_le_length hBl]
    rw [swift.takeWhile_ne_snoc _ y c (fun hm => h2 (by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      exact List.mem_map.mpr ⟨p, List.mem_of_mem_drop hp, rfl⟩))]
    rfl
  refine ⟨by simp, ?_, fun hB => h2 (h8.subset hB), fun hr => ?_, fun z hz => ?_⟩
  · unfold sp.depsIn; rw [hcmd]; simp only; rw [hbef, h3]
  · rw [hkp]; exact h5 (h7.2 hr.symm)
  · rw [hkp] at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact h6 z hz
    · simp at hz; subst hz; exact List.mem_of_getLast? h4

theorem swift.takeWhile_len_lt {α : Type} (q : α → Bool) : ∀ (l : List α), (∃ x ∈ l, q x = false) →
    (l.takeWhile q).length < l.length
  | [], ⟨_, hx, _⟩ => by simp at hx
  | a :: l, ⟨x, hx, hq⟩ => by
    by_cases ha : q a = true
    · have : ∃ x ∈ l, q x = false := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [ha] at hq; cases hq
        · exact ⟨x, hx, hq⟩
      simp only [List.takeWhile_cons, ha, ↓reduceIte, List.length_cons]
      have := swift.takeWhile_len_lt q l this
      omega
    · simp [ha]

theorem swift.lkDeps_len (s : sp.Seq) (c : sp.Cmd) : (sp.lkDeps s c).length ≤ s.length := by
  unfold sp.lkDeps
  simp only
  have hks : ((s.filter (fun p => p.2.key == c.key)).reverse).length ≤ s.length := by
    rw [List.length_reverse]; exact List.length_filter_le _ _
  generalize (s.filter (fun p => p.2.key == c.key)).reverse = ks at hks
  have htw := (List.takeWhile_prefix (p := fun p : sp.CmdId × sp.Cmd => !p.2.isPut) (l := ks)).length_le
  cases hf : ks.find? (fun p => p.2.isPut) with
  | none => split <;> simp <;> omega
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpp := List.find?_some hf
    have hlt := swift.takeWhile_len_lt (fun p : sp.CmdId × sp.Cmd => !p.2.isPut) ks ⟨p, hp, by simp [hpp]⟩
    split <;> simp <;> omega

theorem swift.lkDeps_mem (s : sp.Seq) (c : sp.Cmd) (z : sp.CmdId) (h : z ∈ sp.lkDeps s c) :
    z ∈ s.map Prod.fst := by
  unfold sp.lkDeps at h
  simp only at h
  have hsub : ∀ p ∈ (s.filter (fun p => p.2.key == c.key)).reverse, p.1 ∈ s.map Prod.fst := by
    intro p hp
    rw [List.mem_reverse] at hp
    exact List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩
  generalize (s.filter (fun p => p.2.key == c.key)).reverse = ks at hsub h
  have h1 : ∀ z, z ∈ ((ks.find? (fun p => p.2.isPut)).toList.map Prod.fst) → z ∈ s.map Prod.fst := by
    intro z hz
    cases hf : ks.find? (fun p => p.2.isPut) with
    | none => simp [hf] at hz
    | some p =>
      simp [hf] at hz; subst hz; exact hsub p (List.mem_of_find?_eq_some hf)
  have h2 : ∀ z, z ∈ ((ks.takeWhile (fun p => !p.2.isPut)).map Prod.fst).reverse → z ∈ s.map Prod.fst := by
    intro z hz
    rw [List.mem_reverse] at hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact hsub p (((List.takeWhile_prefix (p := fun p : sp.CmdId × sp.Cmd => !p.2.isPut) (l := ks)).subset hp))
  split at h
  · rcases List.mem_append.mp h with h | h
    · exact h1 z h
    · exact h2 z h
  · exact h1 z h

/-- GAP SWB-13: a proposal's dependencies are fewer than `2^62` and do not contain it, from its
sequence's ids (duplicate-free, small: `IdBound.lean`). -/
theorem swift.propDeps_wf (s : sp.Seq) (y : sp.CmdId) (c : sp.Cmd) (D : List sp.CmdId)
    (hlen : s.length ≤ 6 * 2 ^ 32)
    (h2 : y ∉ (s.dropLast).map Prod.fst) (h3 : D = sp.lkDeps s.dropLast c) :
    D.length < 2 ^ 62 ∧ D ≠ [y] := by
  subst h3
  refine ⟨?_, fun h => h2 (swift.lkDeps_mem _ c y (by rw [h]; simp))⟩
  have := swift.lkDeps_len s.dropLast c
  have : s.dropLast.length = s.length - 1 := List.length_dropLast
  omega

end Perennial.github_com.imdea_software.swiftpaxos
