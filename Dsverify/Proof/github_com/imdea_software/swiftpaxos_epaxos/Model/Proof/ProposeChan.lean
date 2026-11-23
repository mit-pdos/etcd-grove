/-
`handlePropose`'s channel accounting (p-model2): `InvExec.chanOnce` as distinct connection ids
(`ChanOnce`), its stability under sub-channels, the batch's split of its channel (the batch's
ops are distinct and in no other position of the channel: `chan_split`), and the R-CAP case of
`Step.propose` (a full row drops the proposal: the channel shrinks, nothing else moves:
`inv_chan_drop`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HRecover

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace ProposeProof

/-- `InvExec.chanOnce`'s statement. -/
def ChanOnce (C : Nat → List Proposal) : Prop :=
  ∀ (i j n m : Nat) (p p' : Proposal), (C i)[n]? = some p → (C j)[m]? = some p' →
    p.cid = p'.cid → i = j ∧ n = m

theorem chanOnce_nodup {C : Nat → List Proposal} (h : ChanOnce C) (i : Nat) :
    ((C i).map (·.cid)).Nodup := by
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro a b ha hb he
  simp only [List.length_map] at ha hb
  simp only [List.getElem_map] at he
  exact (h i i a b _ _ (List.getElem?_eq_getElem ha) (List.getElem?_eq_getElem hb) he).2

theorem chanOnce_disj {C : Nat → List Proposal} (h : ChanOnce C) {i j : Nat} {p p' : Proposal}
    (hp : p ∈ C i) (hp' : p' ∈ C j) (he : p.cid = p'.cid) : i = j := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hp
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hp'
  exact (h i j n m p p' hn hm he).1

theorem chanOnce_of {C : Nat → List Proposal} (h1 : ∀ i, ((C i).map (·.cid)).Nodup)
    (h2 : ∀ i j p p', p ∈ C i → p' ∈ C j → p.cid = p'.cid → i = j) : ChanOnce C := by
  intro i j n m p p' hn hm he
  have hij := h2 i j p p' (List.mem_of_getElem? hn) (List.mem_of_getElem? hm) he
  subst hij
  refine ⟨rfl, ?_⟩
  obtain ⟨hn', hn2⟩ := List.getElem?_eq_some_iff.mp hn
  obtain ⟨hm', hm2⟩ := List.getElem?_eq_some_iff.mp hm
  refine (h1 i).eq_of_getElem_eq (by simpa using hn') (by simpa using hm') ?_
  simp only [List.getElem_map]
  rw [hn2, hm2]; exact he

theorem chanOnce_sub {C C' : Nat → List Proposal} (h : ChanOnce C)
    (hs : ∀ i, (C' i).Sublist (C i)) : ChanOnce C' :=
  chanOnce_of (fun i => (chanOnce_nodup h i).sublist ((hs i).map _))
    (fun i j p p' hp hp' he => chanOnce_disj h ((hs i).subset hp) ((hs j).subset hp') he)

/-- The batch's split of its channel: its ops are distinct, and distinct from the rest's. -/
theorem chan_split {l b : List Proposal} (hs : b.Subperm l) (hn : (l.map (·.cid)).Nodup) :
    (b.map (·.cid)).Nodup ∧ ∀ p ∈ l.diff b, ∀ p' ∈ b, p.cid ≠ p'.cid := by
  have hp : (b ++ l.diff b).Perm l := List.subperm_append_diff_self_of_count_le (fun x _ => hs.count_le x)
  have h := (hp.map (·.cid)).nodup_iff.mpr hn
  rw [List.map_append, List.nodup_append] at h
  refine ⟨h.1, fun p hp p' hp' he => ?_⟩
  exact h.2.2 _ (List.mem_map_of_mem hp') _ (List.mem_map_of_mem hp) he.symm

/-- `InvExec` when the channels only shrink. -/
theorem invExec_chanSub (S : Sys) (C : Nat → List Proposal) (hX : InvExec S)
    (hC : ∀ j, (C j).Sublist (S.proposeChan j)) : InvExec { S with proposeChan := C } :=
  ⟨hX.reach, hX.ord, hX.gloc, hX.tokSlot,
    fun j p s p' h1 => hX.tokChan j p s p' ((hC j).subset h1),
    chanOnce_sub hX.chanOnce hC, fun j p h => hX.chanOps j p ((hC j).subset h)⟩

/-- **A step that only shrinks the channels keeps the invariant** (the R-CAP case of
`handlePropose`: the row is full, the proposal is dropped). -/
theorem inv_chanSub (S : Sys) (C : Nat → List Proposal) (hS : Inv S)
    (hC : ∀ j, (C j).Sublist (S.proposeChan j)) : Inv { S with proposeChan := C } := by
  refine ⟨?_, AuxProof.aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1
    (AuxProof.frame_same S _ (fun r => rfl) (fun r => rfl) (fun r => rfl) rfl rfl (fun d h => h)
      (fun r => rfl) rfl hS.2 (fun r => ⟨rfl, rfl⟩))
    (PMProof.pm_same hS.2.pm (fun r => rfl) rfl rfl (fun _ _ _ h => h) rfl (fun _ _ _ h => h))
    (invExec_chanSub S C hS.2.exec hC) (AuxProof.execLo_of_eq hS.2.execLo (fun r _ => rfl))⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := hS.1
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩

theorem upd_sub (S : Sys) (i : Nat) (l : List Proposal) (h : l.Sublist (S.proposeChan i)) (j : Nat) :
    (upd S.proposeChan i l j).Sublist (S.proposeChan j) := by
  by_cases hj : j = i
  · subst hj; simp only [upd_same]; exact h
  · simp only [upd_other _ _ _ _ hj]; exact List.Sublist.refl _

/-- **R-CAP: a full row.** -/
theorem inv_propose_full (S : Sys) (i : Nat) (batch : List Proposal) (hS : Inv S)
    (hfull : rowFull (S.rep i) = true) : Inv (S.propose i batch) := by
  have hP : hPropose (S.rep i) batch = (S.rep i, []) := by unfold hPropose; rw [if_pos hfull]
  have : S.propose i batch =
      { S with proposeChan := upd S.proposeChan i ((S.proposeChan i).diff batch) } := by
    unfold Sys.propose
    simp only [hfull, if_true, hP]
    exact RecoverProof.applyStep_same _ i
  rw [this]
  exact inv_chanSub S _ hS (upd_sub S i _ (List.diff_sublist _ _))

end ProposeProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
