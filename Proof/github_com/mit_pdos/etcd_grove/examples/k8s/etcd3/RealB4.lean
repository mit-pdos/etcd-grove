/-
Lean-first (no Rocq counterpart).

# The bridge to Kubernetes' checker, B4: along any linearization (k8s 7g step 4)

`notes/k8s-7g-scope.md` §2.3, B4. For **any** linearization `lin2` of the unary history for `realS` (porcupine's
second run may pick another than the driver's), `NewReplay` succeeds (each step is one `realS` allows) and
`Replay.Validate` accepts every operation: by B3a the replay is the one along the driver's order, which B3b
makes agree with the driver's final configuration (`SimR`, `drive`), hence (`replayAt_prefix`) with each
operation's configuration, where `rvalidateL_point` applies.

- `RunOk h`: what the run needs of a configuration (B1's, the history's, sorted histories, no wrap);
- `replay_of_run`: a run of `realS` is a successful replay;
- `drive`: along the driver's run, the replay of its unary operations tracks the configuration;
- **`realReplay_ok`** (B4).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealValidate

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-- **What the run needs of a configuration**: B1's (`CfgOk`), its history's (`HistCfgOk`), its history's
stores sorted (`HistSorted`), and a revision far from wrapping. -/
def RunOk (h : HSt) : Prop :=
  CfgOk h ∧ HistCfgOk h ∧ HistSorted h.hist ∧ uint.nat h.st.rv < 2 ^ 63

/-- **A run of `realS` is a successful replay** (`NewReplay`'s loop steps exactly as `realS`). -/
theorem replay_of_run (init : RM) : ∀ (l : List (Input × RResp)) (m m' : RM) (ss : GMap w64 RM)
    (cs : List RChange), run (realS init) m l = some m' →
    ∃ acc, l.foldl replayStepL (some (m, ss, cs)) = some acc
  | [], _, _, ss, cs, _ => ⟨_, rfl⟩
  | v :: l, m, m', ss, cs, hr => by
    simp only [run] at hr
    rw [List.foldl_cons]
    by_cases hok : (rstepL v.1 m v.2).1 = true
    · have hs : (realS init).step m v = some (rstepL v.1 m v.2).2.1 := by
        show (if _ then _ else _) = _; rw [if_pos hok]
      rw [hs] at hr
      simp only at hr
      have e : replayStepL (some (m, ss, cs)) v = some ((rstepL v.1 m v.2).2.1,
          <[(rstepL v.1 m v.2).2.1.rv := (rstepL v.1 m v.2).2.1]> ss,
          cs ++ (rstepL v.1 m v.2).2.2.toList) := by
        simp only [replayStepL, hok, ↓reduceIte]
      rw [e]
      exact replay_of_run init l _ m' _ _ hr
    · have hs : (realS init).step m v = none := by
        show (if _ then _ else _) = _; rw [if_neg hok]
      rw [hs] at hr; cases hr

/-- **Along the driver's run** from a single configuration `h` whose replay accumulator tracks it (`SimR`),
the replay of the unary operations succeeds and tracks the final configuration `hF`, and each unary
operation answered at a configuration whose history is a prefix of `hF`'s. -/
theorem drive (h0 : HSt) (H : List (Op ROp)) (hops : ∀ o ∈ H, OpOk o.val)
    (hpres : ∀ o ∈ H, ∀ h, RunOk h → o.val.1.Kind' ≠ W64 5 → RunOk (kstepL o.val.1 h).1) :
    ∀ (l : List ROp), (∀ v ∈ l, ∃ o ∈ H, o.val = v) →
    ∀ (S : linkv.PSet HSt Input) (h : HSt) (acc : RM × GMap w64 RM × List RChange)
      (T : linkv.PSet HSt Input),
      (∀ c, S c ↔ c = ⟨h, []⟩) → RunOk h → SimR h0.st.rv acc h →
      run (kM h0) S l = some T →
      ∃ hF accF, (l.filterMap unaryOf).foldl replayStepL (some acc) = some accF ∧
        SimR h0.st.rv accF hF ∧ RunOk hF ∧ h.hist <+: hF.hist ∧
        ∀ v ∈ l, v.1.Kind' ≠ W64 5 → ∃ hv, RunOk hv ∧ hv.hist <+: hF.hist ∧
          uint.nat h0.st.rv ≤ uint.nat hv.st.rv ∧ v.2.1 = (kstepL v.1 hv).2
  | [], _, _, h, acc, _, _, hrun, hsim, _ =>
    ⟨h, acc, rfl, hsim, hrun, List.prefix_refl _, by simp⟩
  | v :: l, hl, S, h, acc, T, hS, hrun, hsim, hr => by
    obtain ⟨o, ho, hov⟩ := hl v List.mem_cons_self
    have hl' : ∀ w ∈ l, ∃ o ∈ H, o.val = w := fun w hw => hl w (List.mem_cons_of_mem _ hw)
    simp only [run] at hr
    cases hst : (kM h0).step S v with
    | none => rw [hst] at hr; cases hr
    | some S1 =>
      rw [hst] at hr
      simp only at hr
      have hop := hops o ho
      rw [hov] at hop
      have hstep := kM_step h0 h S hS v.1 v.2.1 v.2.2 hop.1 S1 hst
      by_cases hk5 : v.1.Kind' = W64 5
      · obtain ⟨-, hS1⟩ := hstep.1 hk5
        obtain ⟨hF, accF, hfold, hsimF, hrunF, hpre, hpts⟩ :=
          drive h0 H hops hpres l hl' S1 h acc T hS1 hrun hsim hr
        refine ⟨hF, accF, ?_, hsimF, hrunF, hpre, ?_⟩
        · rw [List.filterMap_cons]; simp only [unaryOf, hk5, ↓reduceIte]; exact hfold
        · intro w hw hw5
          rcases List.mem_cons.1 hw with rfl | hw
          · exact absurd hk5 hw5
          · exact hpts w hw hw5
      · obtain ⟨hy, hS1⟩ := hstep.2 hk5
        have hrun' := hpres o ho h hrun (by rw [hov]; exact hk5)
        rw [hov] at hrun'
        obtain ⟨hcfg, hhc, hsort, hrvb⟩ := hrun
        obtain ⟨hok, hmv⟩ := rstepL_kstepL v.1 v.2.1 v.2.2 h hk5 hop hcfg hy
        obtain ⟨m, ss, cs⟩ := acc
        have hm : m = absR h.st := hsim.1
        subst hm
        have hrs : replayStepL (some (absR h.st, ss, cs)) (v.1, v.2.2) =
            some ((rstepL v.1 (absR h.st) v.2.2).2.1,
              <[(rstepL v.1 (absR h.st) v.2.2).2.1.rv := (rstepL v.1 (absR h.st) v.2.2).2.1]> ss,
              cs ++ (rstepL v.1 (absR h.st) v.2.2).2.2.toList) := by
          simp only [replayStepL, hok, ↓reduceIte]
        have hsim' := simR_step h0.st.rv _ h v.1 v.2.2 _ hsim hhc.1 hhc.2.1 hrun'.2.2.1 hrun'.2.1.1
          hrun'.2.2.2 hrs hmv
        obtain ⟨hF, accF, hfold, hsimF, hrunF, hpre, hpts⟩ :=
          drive h0 H hops hpres l hl' S1 _ _ T hS1 hrun' hsim' hr
        have hpre0 : h.hist <+: (kstepL v.1 h).1.hist := by
          rw [kstepL_hist]
          split
          · exact List.prefix_refl _
          · exact List.prefix_append _ _
        refine ⟨hF, accF, ?_, hsimF, hrunF, hpre0.trans hpre, ?_⟩
        · rw [List.filterMap_cons]
          simp only [unaryOf, hk5, ↓reduceIte, List.foldl_cons]
          rw [hrs]; exact hfold
        · intro w hw hw5
          rcases List.mem_cons.1 hw with rfl | hw
          · exact ⟨h, ⟨hcfg, hhc, hsort, hrvb⟩, hpre0.trans hpre, hsim.2.1, hy⟩
          · exact hpts w hw hw5

/-- **B4: the replay's checks pass along any linearization.** On a recorded history as in B2, linearized by
`π` for the driver's model from the seeded configuration `h0`, for **any** linearization `lin2` of its unary
operations for `realS` from `h0`'s abstraction, `NewReplay` along `lin2` succeeds and `Replay.Validate`
accepts every operation. Premises beyond B2's: the configurations' histories (`RunOk`, kept by every unary
step), the floor (`FloorOk`), and a history short enough that the revisions do not wrap. -/
theorem realReplay_ok (h0 : HSt) (H : List (Op ROp)) (π : List Nat)
    (hπ : IsLinearization (kM h0) H π) (hops : ∀ o ∈ H, OpOk o.val) (hrun0 : RunOk h0)
    (hpres : ∀ o ∈ H, ∀ h, RunOk h → o.val.1.Kind' ≠ W64 5 → RunOk (kstepL o.val.1 h).1)
    (hfl : ∀ o ∈ H, FloorOk h0.st.rv o.val.1) (hn : uint.nat h0.st.rv + H.length < 2 ^ 64)
    (lin2 : List Nat) (h2 : IsLinearization (realS (absR h0.st)) (fmapH unaryOf H) lin2) :
    ∃ R, replayL (absR h0.st) (vals (fmapH unaryOf H) lin2) = some R ∧
      ∀ op ∈ vals (fmapH unaryOf H) lin2, rvalidateL R op.1 op.2 = true := by
  have hmemH : ∀ v ∈ vals H π, ∃ o ∈ H, o.val = v := by
    intro v hv
    obtain ⟨k, -, hk⟩ := List.mem_filterMap.1 hv
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hk
    exact ⟨o, List.mem_of_getElem? ho, rfl⟩
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 hπ.2.2.1
  have hsim0 := simR_init h0 hrun0.2.1.1 hrun0.2.1.2.1 hrun0.1.2.2.1
  obtain ⟨hF, accF, hfold, hsimF, hrunF, -, hpts⟩ := drive h0 H hops hpres (vals H π) hmemH
    (kM h0).init h0 _ T (fun c => Iff.rfl) hrun0 hsim0 hT
  have hR1 : replayL (absR h0.st) ((vals H π).filterMap unaryOf) = some ⟨accF.2.1, accF.2.2⟩ := by
    unfold replayL; erw [hfold]; rfl
  obtain ⟨m2, hm2⟩ := Option.isSome_iff_exists.1 h2.2.2.1
  obtain ⟨acc2, hacc2⟩ := replay_of_run (absR h0.st) _ _ m2 {[(absR h0.st).rv := absR h0.st]} [] hm2
  have hR2 : replayL (absR h0.st) (vals (fmapH unaryOf H) lin2) = some ⟨acc2.2.1, acc2.2.2⟩ := by
    unfold replayL; erw [hacc2]; rfl
  have hperm : ((vals H π).filterMap unaryOf).Perm (vals (fmapH unaryOf H) lin2) := by
    have p2 := isLinearization_perm h2
    rw [fmapH_map_val] at p2
    exact ((isLinearization_perm hπ).filterMap _).trans p2.symm
  have hlen : ((vals H π).filterMap unaryOf).length ≤ H.length := by
    rw [(hperm.trans (isLinearization_perm h2)).length_eq, List.length_map]
    unfold fmapH; exact List.length_filterMap_le _ _
  have heq := replayL_perm (absR h0.st) _ _ _ _ hrun0.1.2.2.1 (by rw [absR_rv]; omega) hperm hR1 hR2
  refine ⟨_, hR2, ?_⟩
  rw [← heq]
  intro op hop
  obtain ⟨v, hv, hvu⟩ := List.mem_filterMap.1 (hperm.mem_iff.2 hop)
  have hk5 : v.1.Kind' ≠ W64 5 := by
    intro e; unfold unaryOf at hvu; rw [if_pos e] at hvu; cases hvu
  have hop' : op = (v.1, v.2.2) := by
    unfold unaryOf at hvu; rw [if_neg hk5] at hvu; exact (Option.some.inj hvu).symm
  subst hop'
  obtain ⟨hv', hrv, hpre, hs0, hy⟩ := hpts v hv hk5
  obtain ⟨o, ho, rfl⟩ := hmemH v hv
  have hRv := replayAt_prefix _ _ hv' hF hsimF.2.2.2.2.2 hpre hrv.2.1.1 hrunF.2.1.1
  exact rvalidateL_point h0.st.rv _ hv' o.val.1 o.val.2.1 o.val.2.2 hk5 (hops o ho) hrv.1 hrv.2.1 hRv hs0
    (hfl o ho) hy

end go

end k8s_correctness
end EtcdGrove
end Perennial
