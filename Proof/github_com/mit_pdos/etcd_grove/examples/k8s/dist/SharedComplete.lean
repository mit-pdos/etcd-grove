/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: `FullComplete`

`notes/k8s-dist-k4.md`, "Handoff K4-4", step 6. By induction on the semantic model's run (`SRun`),
the search's configuration related to the cluster's (`CRel`): the silent steps before an operation
are `settle` (`CRel.reach`), then the operation's step from the search skipped to its target: a
watch by `HRel.watchOk`, a failed call as on the cluster, a successful one by `CRel.ok`.

**WIP (K4-5)**: `CRel.ok` (a successful non-watch operation) is `sorry`; `notes/k8s-dist-k4.md`,
"Handoff K4-5".
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedSettle

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section go
variable [GooseExts]

theorem evMaxL_foldl_le (m : Nat) : ∀ (l : List WEv) (acc : Nat), acc ≤ m →
    (∀ e ∈ l, uint.nat e.o.ResourceVersion' ≤ m) →
    l.foldl (fun t e => max t (uint.nat e.o.ResourceVersion')) acc ≤ m
  | [], _, ha, _ => ha
  | e :: l, acc, ha, he => by
    rw [List.foldl_cons]
    exact evMaxL_foldl_le m l _ (by have := he e List.mem_cons_self; omega)
      (fun e' h' => he e' (List.mem_cons_of_mem _ h'))

/-- **A watch the cluster allows has its target at most the cluster's revision.** -/
theorem watchOkL_target (x : Input) (y : Output) (h : HSt) (hk : x.Kind' = W64 5) (r : Nat)
    (hok : watchOkL x y h = true) : targetL x y r ≤ uint.nat h.st.rv := by
  unfold targetL; rw [if_pos hk]
  unfold watchOkL at hok
  by_cases hf : (y.WFailed' || x.Skip') = true
  · rw [if_pos hf]; exact Nat.zero_le _
  rw [if_neg hf] at hok ⊢
  rcases hd : decWEventsL y.WEvents' with _ | all
  · exact Nat.zero_le _
  rw [hd] at hok
  dsimp only at hok ⊢
  by_cases h5 : all.any (fun e => 5 ≤ e.t) = true
  · rw [if_pos h5] at hok; cases hok
  rw [if_neg h5] at hok
  have h5' : ∀ e ∈ all, e.t < 5 := fun e he => by
    have := List.any_eq_false.mp (Bool.eq_false_iff.mpr h5) e he; simp at this; omega
  by_cases hrc : (all.filter fun e => e.t ≠ 4).any
      (fun e => uint.nat h.st.rv < uint.nat e.o.ResourceVersion') = true
  · rw [if_pos hrc] at hok; cases hok
  rw [if_neg hrc] at hok
  have hle : ∀ e ∈ all, e.t < 4 → uint.nat e.o.ResourceVersion' ≤ uint.nat h.st.rv := fun e he ht => by
    have := List.any_eq_false.mp (Bool.eq_false_iff.mpr hrc) e
      (List.mem_filter.mpr ⟨he, by simp; omega⟩)
    simp at this; omega
  have hmax : evMaxL all ≤ uint.nat h.st.rv :=
    evMaxL_foldl_le _ _ 0 (Nat.zero_le _) (fun e he => by
      have he' := List.mem_filter.mp he
      exact hle e he'.1 (by simpa using he'.2))
  by_cases hsi : x.SendInit' = W64 2 ∧ all.any (fun e => e.t < 4) = true
  · rw [if_pos hsi]
    rcases hp : parseRVD x.MinRV' with _ | req
    · exact hmax
    dsimp only
    refine Nat.max_le.mpr ⟨hmax, ?_⟩
    obtain ⟨e0, he0, ht0⟩ := List.any_eq_true.mp hsi.2
    have hne : (all.filter fun e => e.t ≠ 4) ≠ [] := by
      intro hnil
      have : e0 ∈ all.filter (fun e => e.t ≠ 4) := List.mem_filter.mpr ⟨he0, by simp at ht0 ⊢; omega⟩
      rw [hnil] at this; cases this
    generalize all.filter (fun e => e.t ≠ 4) = evs at hok hne
    by_cases hbm : (!bookmarksOkL evs) = true
    · rw [if_pos hbm] at hok; cases hok
    rw [if_neg hbm, hp] at hok
    dsimp only at hok
    rw [if_pos hsi.1] at hok
    rcases hb : evs.findIdx? (fun e => e.t = 3) with _ | b
    · rw [hb] at hok
      unfold initialPrefixOkL at hok
      have he : evs.isEmpty = false := by cases evs; exact absurd rfl hne; rfl
      rw [he, Bool.false_or] at hok
      obtain ⟨r', hr', _⟩ := List.any_eq_true.mp hok
      have := List.mem_range'_1.mp hr'
      omega
    · rw [hb] at hok
      dsimp only at hok
      generalize evs.getD b ⟨0, ⟨[], [], [], [], [], [], 0, false⟩⟩ = bm at hok
      by_cases ha : (!bm.o.Annotated') = true
      · rw [if_pos ha] at hok; cases hok
      rw [if_neg ha] at hok
      by_cases hc1 : (uint.nat req ≠ 0 ∧ uint.nat bm.o.ResourceVersion' < uint.nat req) ∨
          uint.nat bm.o.ResourceVersion' < 1 ∨ uint.nat h.st.rv < uint.nat bm.o.ResourceVersion'
      · rw [if_pos hc1] at hok; cases hok
      omega
  · rw [if_neg hsi]; exact hmax

section rel
variable {A : List Nat} {n0 : Nat}

/-- **WIP (K4-5): a successful operation other than a watch**, from the search's configuration `d`
skipped to its target, answers as the cluster's and keeps the relation. Plan: `notes/k8s-dist-k4.md`,
"Handoff K4-5". -/
theorem CRel.ok (hn0 : 1 ≤ n0) {d g : GCfg} (hc : CRel A n0 d g) (hnw : NoWrap g) (x : Input) (y : Output)
    (hk : x.Kind' ≠ W64 5) (hy : y = (kstepL x g.st).2) (h4 : y.Err' ≠ W64 4) (hanc : OpAnchors A x y) :
    ∃ e', e' ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x y ∧
      CRel A n0 e' ⟨(kstepL x g.st).1, g.pend⟩ := by
  sorry

/-- A failed call's target is 0. -/
theorem targetL_err (x : Input) (y : Output) (r : Nat) (hk : x.Kind' ≠ W64 5) (h4 : y.Err' = W64 4) :
    targetL x y r = 0 := by
  unfold targetL
  rw [if_neg hk, if_neg (by rw [h4]; decide), if_pos (by rw [h4]; decide)]

/-- **One operation**: the cluster's silent steps, then its step, are a step of the search. -/
theorem CRel.op (hn0 : 1 ≤ n0) {h0 : HSt} {e g g₁ g₂ : GCfg} {x : Input} {y : Output}
    (hc : CRel A n0 e g) (hr : SReach h0 g g₁) (hnw : NoWrap g₁)
    (hps : linkv.PStep (kSpec h0) g₁ x (ansOf y) g₂) (hanc : OpAnchors A x y) :
    ∃ e', SearchStep A e x y e' ∧ CRel A n0 e' g₂ := by
  obtain ⟨d, hsd, hcd⟩ := CRel.reach hr hc
  suffices ∃ e', e' ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x y ∧
      CRel A n0 e' g₂ by
    obtain ⟨e', he', hc'⟩ := this; exact ⟨e', ⟨d, hsd, he'⟩, hc'⟩
  generalize ha : ansOf y = a at hps
  unfold ansOf at ha
  cases hps with
  | ok ho =>
    have hk : x.Kind' ≠ W64 5 := by simpa using ho
    split at ha
    · cases ha
    · next h4 =>
      cases ha
      exact hcd.ok hn0 hnw x _ hk rfl h4 hanc
  | errW hw ho =>
    have hk : x.Kind' ≠ W64 5 := by simpa using ho
    split at ha
    · next h4 =>
      obtain ⟨⟨ρ, W, h⟩, hp, hpw, hpa⟩ := hcd
      refine ⟨⟨d.st, x :: d.pend⟩, ?_, ⟨⟨ρ, W, h⟩, hp.cons x, ?_, ?_⟩⟩
      · rw [targetL_err x y _ hk h4, skipToL_le _ _ (Nat.zero_le _)]
        unfold stepL; rw [if_neg hk, if_pos h4, if_pos hw]; exact List.mem_singleton_self _
      · intro i hi; rcases List.mem_cons.mp hi with rfl | hi
        · exact hw
        · exact hpw i hi
      · intro i hi; rcases List.mem_cons.mp hi with rfl | hi
        · exact hanc.2.1
        · exact hpa i hi
    · cases ha
  | errR hw ho =>
    have hk : x.Kind' ≠ W64 5 := by simpa using ho
    split at ha
    · next h4 =>
      refine ⟨d, ?_, hcd⟩
      rw [targetL_err x y _ hk h4, skipToL_le _ _ (Nat.zero_le _)]
      unfold stepL; rw [if_neg hk, if_pos h4, if_neg (by simpa using hw)]; exact List.mem_singleton_self _
    · cases ha
  | obs o hob hoo =>
    have hk : x.Kind' = W64 5 := by simpa using hob
    have hoy : o = y := by
      split at ha
      · cases ha
      · cases ha; rfl
    subst hoy
    have hw : watchOkL x o g₁.st = true := hoo
    obtain ⟨⟨ρ, W, h⟩, hp, hpw, hpa⟩ := hcd
    have ht := watchOkL_target x o g₁.st hk (uint.nat d.st.st.rv) hw
    have h' := h.skipTo _ ht
    have hlt : uint.nat g₁.st.st.rv < 2 ^ 64 := by word
    have hsrv := skipToL_rv d.st (targetL x o (uint.nat d.st.st.rv)) (by omega)
    have ht0 : targetL x o 0 = targetL x o (uint.nat d.st.st.rv) := by unfold targetL; rw [if_pos hk, if_pos hk]
    have hws := h'.watchOk hn0 x o hanc hk (by rw [ht0, hsrv]; exact Nat.le_max_right _ _) hw
    refine ⟨⟨skipToL d.st (targetL x o (uint.nat d.st.st.rv)), d.pend⟩, ?_, ⟨⟨ρ, W, h'⟩, hp, hpw, hpa⟩⟩
    unfold stepL; rw [if_pos hk, if_pos hws]; exact List.mem_singleton_self _

end rel

/-- **K4's theorem** (WIP: `CRel.ok`). -/
theorem fullComplete : FullComplete := by
  intro h0 A ops c' hlen hlast hseed _ hA hrun
  have hn0 : 1 ≤ uint.nat h0.st.rv := by
    rw [← hlen]
    cases hh : h0.hist with
    | nil => rw [hh] at hlast; cases hlast
    | cons _ _ => simp
  have hinit : CRel A (uint.nat h0.st.rv) ⟨h0, []⟩ ⟨h0, []⟩ :=
    ⟨⟨id, [], HRel.init h0 hlen hlast hseed⟩, List.Perm.refl _, by simp, by simp⟩
  have main : ∀ c ops c', SRun h0 c ops c' → ∀ e, CRel A (uint.nat h0.st.rv) e c →
      (∀ p ∈ ops, OpAnchors A p.1 p.2) → SearchRun A e ops := by
    intro c ops c' hr
    induction hr with
    | nil => intro e _ _; exact .nil _
    | cons hre hnw hps _ ih =>
      intro e hc hops
      obtain ⟨e', hst, hc'⟩ := hc.op hn0 hre hnw hps (hops _ List.mem_cons_self)
      exact .cons hst (ih e' hc' (fun p hp => hops p (List.mem_cons_of_mem _ hp)))
  exact main _ _ _ hrun _ hinit hA.2

end go

end k8s_dist
end EtcdGrove
end Perennial
