/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Follower.lean (241f27e).
-/
/-
`proto` — the follower's log writes: `truncate` and `followerStore` preserve `PInv`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.SrvFrame

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-- The state with server `i`'s log replaced. -/
abbrev setLog (σ : PState) (i : SID) (L' : RLog) : PState := setSrv σ i { σ.srv i with log := L' }

theorem setLog_srv_eq (σ : PState) (i : SID) (L' : RLog) (j : SID) :
    ((setLog σ i L').srv j).term = (σ.srv j).term ∧ ((setLog σ i L').srv j).vterm = (σ.srv j).vterm ∧
    ((setLog σ i L').srv j).vcand = (σ.srv j).vcand ∧ ((setLog σ i L').srv j).dur = (σ.srv j).dur ∧
    ((setLog σ i L').srv j).cidx = (σ.srv j).cidx := by
  rw [setSrv_srv]; split <;> (subst_vars; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem setLog_term (σ : PState) (i : SID) (L' : RLog) (j : SID) :
    (setLog σ i L').term j = σ.term j := (setLog_srv_eq σ i L' j).1

/-- A step that only replaces server `i`'s log by a log `L'` with the per-log properties keeps
`PInv`, given `IAcks` and `IDur` of the new state. -/
theorem setLog_inv {σ : PState} {i : SID} {L' : RLog} (h : PInv σ) (hi : i ∈ σ.srvs)
    (hLM : LMok σ L') (hg1 : L' = [] ∨ ent L' 1 = some σ.g)
    (hne : L' ≠ [] → 1 ≤ σ.term i)
    (hcur : σ.leader (σ.term i) = some i → L' = σ.llog (σ.term i))
    (hb : L'.length ≤ σ.maxI) (hterms : ∀ k, 1 ≤ k → k ≤ L'.length → termAt L' k ≤ σ.term i)
    (hA' : IAcks (setLog σ i L')) (hD' : IDur (setLog σ i L')) :
    PInv (setLog σ i L') ∧ Grows σ (setLog σ i L') := by
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hPb, hR⟩ := h
  have hlog := setSrv_log σ i { σ.srv i with log := L' }
  have htm := setLog_term σ i L'
  refine ⟨⟨hG, hL, ?_, ?_, ?_, hA', hVA, hLC, hCo, hD', ?_, ?_,
    IPub_grow (σ := σ) (HG.refl_llog rfl rfl rfl rfl rfl) (fun j _ => by rw [htm]; exact Nat.le_refl _)
      (fun j _ => by rw [(setLog_srv_eq σ i L' j).2.2.2.1]) (fun _ _ _ x => x) rfl hPb, hR⟩, ?_⟩
  · obtain ⟨l1, l2, l3, l4, l5⟩ := hLo
    refine ⟨fun j hj => ?_, l2, l3, l4, l5⟩
    rw [hlog]; split
    · exact ⟨hLM, hg1⟩
    · exact l1 j hj
  · intro j hj hl
    rw [htm] at hl ⊢
    rw [hlog]; split
    · subst_vars; exact hcur hl
    · exact hC j hj hl
  · exact IVotes_srv (σ := σ) rfl rfl rfl rfl
      (fun j => ⟨(setLog_srv_eq σ i L' j).2.1, (setLog_srv_eq σ i L' j).2.2.1⟩)
      (fun j => by rw [htm]; exact Nat.le_refl _) hV
  · obtain ⟨b1, b2, b3, b4, b5⟩ := hB
    refine ⟨fun j hj => ?_, b2, b3, b4, b5⟩
    rw [hlog, htm]; split
    · subst_vars; exact ⟨(b1 _ hj).1, hb⟩
    · exact b1 j hj
  · intro j hj
    rw [hlog, htm]; split
    · subst_vars; exact ⟨hne, hterms⟩
    · exact hX j hj
  · refine ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
      fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
      fun j => ?_, fun j => ?_, Nat.le_refl _, Nat.le_refl _, fun _ _ x => x,
      fun _ _ _ _ x => Or.inl x⟩
    · rw [htm]; exact Nat.le_refl _
    · rw [(setLog_srv_eq σ i L' j).2.2.2.1]; exact Nat.le_refl _

/-! ### followerStore -/

section
variable {σ : PState} {i : SID} {prev pt : Nat} {ents : RLog} {lci j : Nat}
  (h : PInv σ) (hp : followerStorePre σ i prev pt ents lci j)
include h hp

theorem fs_log_eq :
    σ.log i ++ ents.drop j = (σ.llog (σ.term i)).take (prev + ents.length) := by
  obtain ⟨hi, hae, hpm, hm, hj, hlen⟩ := hp
  have hag := ae_agree_upto h.2.2.1 hi hae hpm hm (by omega)
  exact fs_log hae hag hlen hm.1

theorem followerStore_inv' :
    PInv (followerStore σ i (ents.drop j)) ∧ Grows σ (followerStore σ i (ents.drop j)) := by
  have heq := fs_log_eq h hp
  have hgL : HG σ (followerStore σ i (ents.drop j)) := HG.refl_llog rfl rfl rfl rfl rfl
  have hlogs : ∀ j' ∈ σ.srvs, σ.log j' <+: (followerStore σ i (ents.drop j)).log j' := by
    intro j' _
    show σ.log j' <+: (setLog σ i (σ.log i ++ ents.drop j)).log j'
    rw [setSrv_log]; split
    · subst_vars; exact List.prefix_append _ _
    · exact List.prefix_refl _
  have hterm : ∀ j' ∈ σ.srvs, σ.term j' ≤ (followerStore σ i (ents.drop j)).term j' := by
    intro j' _; show _ ≤ (setLog σ i _).term j'; rw [setLog_term]; exact Nat.le_refl _
  obtain ⟨hi, hae, hpm, hm, hj, hlen⟩ := hp
  have hP := h
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, _⟩ := h
  have hpl : σ.log i ++ ents.drop j <+: σ.llog (σ.term i) := by rw [heq]; exact List.take_prefix _ _
  have hT2 := leader_ge_two hL hae.1
  apply setLog_inv hP hi
  · rw [heq]; exact LMok_take (hLo.2.1 _) _
  · right
    rw [heq, ent_take _ _ _ (by omega)]
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hae.1
    exact (hL.1 _ ℓ hℓ).2.2.2.2.1
  · intro _; omega
  · intro hl
    exfalso
    have := hC i hi hl
    have h1 := hae.2.1
    have h2 := congrArg List.length heq
    simp only [List.length_append, List.length_drop, List.length_take] at h2
    rw [this] at hlen
    omega
  · exact Nat.le_trans hpl.length_le (hB.2.1 _)
  · intro k h1 h2
    rw [← termAt_grow hpl h2]
    exact llog_term_le hG hL h1 (Nat.le_trans h2 hpl.length_le)
  · exact IAcks_grow hgL hL hlogs hterm (fun _ _ _ x => x) hA
  · exact IDur_grow hgL hlogs hterm (fun j' _ => ⟨(setLog_srv_eq σ i _ j').2.2.2.1,
      (setLog_srv_eq σ i _ j').2.2.2.2⟩) (fun _ _ _ x => x) hD

end

/-! ### truncate -/

section
variable {σ : PState} {i : SID} {prev pt : Nat} {ents : RLog} {lci j : Nat}
  (h : PInv σ) (hp : truncatePre σ i prev pt ents lci j)
include h hp

/-- The conflict is with the leader log's entry. -/
theorem tr_conflict :
    prev + 1 + j ≤ (σ.llog (σ.term i)).length ∧
    termAt (σ.log i) (prev + 1 + j) ≠ termAt (σ.llog (σ.term i)) (prev + 1 + j) := by
  obtain ⟨hi, hae, hpm, hm, hj, hlen, hne⟩ := hp
  refine ⟨by have := hae.2.1; omega, ?_⟩
  rw [ae_slice_term hae (by omega) (by omega)] at hne
  have e : prev + (j + 1) = prev + 1 + j := by omega
  rw [e] at hne
  exact hne

theorem tr_ge_two : 1 ≤ prev + j := by
  have ⟨hc1, hc2⟩ := tr_conflict h hp
  obtain ⟨hi, hae, _⟩ := id hp
  apply Classical.byContradiction
  intro hz
  have e : prev + 1 + j = 1 := by omega
  rw [e] at hc2
  obtain ⟨hG, hL, hLo, _⟩ := h
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hae.1
  rcases (hLo.1 i hi).2 with h0 | h0
  · obtain ⟨_, _, _, _, _, hlen, _⟩ := hp
    rw [h0] at hlen; simp at hlen
  · rw [termAt_of_ent h0, termAt_of_ent (hL.1 _ ℓ hℓ).2.2.2.2.1] at hc2
    exact hc2 rfl

/-- A truncation never reaches the durable prefix. -/
theorem tr_gt_dur : (σ.srv i).dur.1 < prev + 1 + j := by
  have ⟨hc1, hc2⟩ := tr_conflict h hp
  obtain ⟨hi, hae, _⟩ := hp
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, _⟩ := h
  apply Classical.byContradiction
  intro hn
  rcases (hD i hi).1 with hd | ⟨hT, ⟨k', p', hk', hck⟩, hag⟩
  · omega
  · have e1 := agree_termAt hag (show prev + 1 + j ≤ (σ.srv i).dur.1 by omega)
    have hcm := (hCo.1 _ _ _ hck).1
    rcases Nat.lt_or_eq_of_le hT with hlt | heq
    · have := hLC _ _ _ hcm (hCo.1 _ _ _ hck).2.1 _ hlt hae.1
      unfold lacks at this
      have ⟨_, hag2⟩ := Classical.not_not.mp this
      have e2 := agree_termAt hag2 (show prev + 1 + j ≤ k' by omega)
      exact hc2 (e1.trans e2.symm)
    · rw [heq] at e1
      exact hc2 e1

theorem tr_IAcks : IAcks (setLog σ i ((σ.log i).take (prev + 1 + j - 1))) := by
  have ⟨hc1, hc2⟩ := tr_conflict h hp
  obtain ⟨hi, hae, _⟩ := hp
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, _⟩ := h
  intro j' T m ha
  obtain ⟨hj', hld, hm, hT, hk⟩ := hA j' T m ha
  rw [setLog_term]
  refine ⟨hj', hld, hm, hT, fun k hkm => ?_⟩
  rw [setSrv_log]
  split
  · subst_vars
    rcases hk k hkm with hag | hr
    · by_cases hkc : k ≤ prev + j
      · exact Or.inl (agree_take_left _ hag (by omega))
      · right
        have e1 := agree_termAt hag (show prev + 1 + j ≤ k by omega)
        have hTne : T ≠ σ.term j' := by
          intro e; rw [e] at e1; exact hc2 e1
        refine ⟨σ.term j', by omega, Nat.le_refl _, hae.1, ?_⟩
        intro ⟨_, hag2⟩
        exact hc2 (e1.trans (agree_termAt hag2 (show prev + 1 + j ≤ k by omega)).symm)
    · exact Or.inr hr
  · exact hk k hkm

end

theorem truncate_inv' (σ : PState) (i : SID) (prev pt : Nat) (ents : RLog) (lci j : Nat)
    (h : PInv σ) (hp : truncatePre σ i prev pt ents lci j) :
    PInv (truncate σ i (prev + 1 + j)) ∧ Grows σ (truncate σ i (prev + 1 + j)) := by
  have hge := tr_ge_two h hp
  have hdur := tr_gt_dur h hp
  have hA' := tr_IAcks h hp
  have hcur := tr_conflict h hp
  obtain ⟨hi, hae, hpm, hm, hj, hlen, hne⟩ := hp
  have hP := h
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, _⟩ := h
  have hpl : (σ.log i).take (prev + 1 + j - 1) <+: σ.log i := List.take_prefix _ _
  show PInv (setLog σ i _) ∧ Grows σ (setLog σ i _)
  apply setLog_inv hP hi (LMok_take (hLo.1 i hi).1 _)
  · rcases (hLo.1 i hi).2 with h0 | h0
    · left; rw [h0]; simp
    · right; rw [ent_take _ _ _ (by omega)]; exact h0
  · intro hne'
    apply (hX i hi).1
    intro h0; rw [h0] at hne'; exact hne' (by simp)
  · intro hl
    exfalso
    have := hC i hi hl
    rw [this] at hcur
    exact hcur.2 rfl
  · exact Nat.le_trans hpl.length_le ((hB.1 i hi).2)
  · intro k h1 h2
    rw [← termAt_grow hpl h2]
    exact (hX i hi).2 k h1 (Nat.le_trans h2 hpl.length_le)
  · exact hA'
  · intro i' hi'
    rw [(setLog_srv_eq σ i _ i').2.2.2.1, (setLog_srv_eq σ i _ i').2.2.2.2, setLog_term, setSrv_log]
    obtain ⟨hd, hcx⟩ := hD i' hi'
    refine ⟨?_, hcx⟩
    rcases hd with hd | ⟨a, b, c⟩
    · exact Or.inl hd
    · refine Or.inr ⟨a, b, ?_⟩
      split
      · subst_vars; exact agree_take_left _ c (by omega)
      · exact c

end proto
end github_com.hashicorp.raft
end Perennial
