/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: the cluster's silent steps as the search's `settle`

`notes/k8s-dist-k4.md`, "Handoff K4-4", step 5. The search's configuration and the cluster's are
related (`CRel`: `HRel` on the stores, the pending writes the same up to order, each a write whose
resource-version precondition is an anchor). Each silent step of the cluster is matched by `settle`
(`SettleL`): a foreign revision by nothing, a reordering by nothing, a pending write that changes
nothing by `drop`, one the cluster puts at `R` by `land` at `canonL A rv R` (`SharedPlace.lean`),
the search skipped to the revision before it (`CRel.silent`, `CRel.reach`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedHist

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

theorem SettleL.trans {A : List Nat} {c d e : GCfg} (h1 : SettleL A c d) (h2 : SettleL A d e) :
    SettleL A c e := by
  induction h1 with
  | refl => exact h2
  | drop i hi hs _ ih => exact .drop i hi hs (ih h2)
  | land i l hi hs hl hl64 _ ih => exact .land i l hi hs hl hl64 (ih h2)

/-- **The search's configuration `e` and the cluster's `g`**: the stores related by `HRel` from the
seeds at `n0`, the pending writes the same up to order, each a write with an anchored precondition. -/
structure CRel (A : List Nat) (n0 : Nat) (e g : GCfg) : Prop where
  rel : ∃ ρ W, HRel A n0 ρ W e.st g.st
  perm : e.pend.Perm g.pend
  pw : ∀ i ∈ g.pend, isWriteL i = true
  pa : ∀ i ∈ g.pend, i.HasPreRV' = true → ∀ r, parseRVD i.PreRV' = some r → uint.nat r ∈ A

/-- `removeAtL` at the first occurrence is `erase`. -/
theorem removeAtL_idxOf (l : List Input) (i : Input) : removeAtL l (l.idxOf i) = l.erase i := by
  rw [List.erase_eq_eraseIdx_of_idxOf rfl, List.eraseIdx_eq_take_drop_succ]; rfl

theorem pendAt_idxOf (e : GCfg) (i : Input) (hi : i ∈ e.pend) : pendAt e (e.pend.idxOf i) = i := by
  have hl := List.idxOf_lt_length_of_mem hi
  unfold pendAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some, List.getElem_idxOf hl]

/-- **One silent step of the cluster is a `settle` of the search.** -/
theorem CRel.silent {A : List Nat} {n0 : Nat} {h0 : HSt} {e g g₁ : GCfg} (hc : CRel A n0 e g)
    (hs : SSilent h0 g g₁) : ∃ e₁, SettleL A e e₁ ∧ CRel A n0 e₁ g₁ := by
  obtain ⟨⟨ρ, W, h⟩, hp, hpw, hpa⟩ := hc
  cases hs with
  | foreign hnw => exact ⟨e, .refl _, ⟨⟨ρ, W, h.foreign_c hnw⟩, hp, hpw, hpa⟩⟩
  | pend hnw hps =>
    cases hps with
    | perm p hpp =>
      exact ⟨e, .refl _, ⟨⟨ρ, W, h⟩, hp.trans hpp.symm, fun i hi => hpw i (hpp.mem_iff.mp hi),
        fun i hi => hpa i (hpp.mem_iff.mp hi)⟩⟩
    | apply i hi =>
      have hie : i ∈ e.pend := hp.mem_iff.mpr hi
      have hidx := List.idxOf_lt_length_of_mem hie
      have hat := pendAt_idxOf e i hie
      have hrm : (removeAtL e.pend (e.pend.idxOf i)).Perm (g.pend.erase i) := by
        rw [removeAtL_idxOf]; exact hp.erase i
      have hw := hpw i hi
      have hpre := hpa i hi
      have hpw' : ∀ j ∈ g.pend.erase i, isWriteL j = true := fun j hj => hpw j (List.mem_of_mem_erase hj)
      have hpa' : ∀ j ∈ g.pend.erase i, j.HasPreRV' = true → ∀ r, parseRVD j.PreRV' = some r →
          uint.nat r ∈ A := fun j hj => hpa j (List.mem_of_mem_erase hj)
      have hb : uint.nat g.st.st.rv + 1 < 2 ^ 64 := hnw
      show ∃ e₁, SettleL A e e₁ ∧ CRel A n0 e₁ ⟨(kstepL i g.st).1, g.pend.erase i⟩
      rw [kstepL_write i g.st hw]
      obtain ⟨_, hrv⟩ := h.stepRen i hpre hb
      by_cases hch : (mstepL i g.st.st).1.rv = g.st.st.rv
      · -- no effect: `drop`
        have hsame : (mstepL i e.st.st).1.rv = e.st.st.rv := by
          rcases hrv with ⟨e1, _⟩ | ⟨_, e2⟩
          · exact e1
          · exact absurd (e2.symm.trans hch) (rv_succ_ne _)
        refine ⟨⟨e.st, removeAtL e.pend (e.pend.idxOf i)⟩,
          .drop _ hidx (by rw [hat]; exact hsame) (.refl _), ⟨⟨ρ, W, ?_⟩, hrm, hpw', hpa'⟩⟩
        rw [advanceL_same _ _ (mstepL_same i _ hch)]; exact h
      · -- the cluster puts it at `R = rv + 1`: land at `canonL`
        have hch' : (mstepL i e.st.st).1.rv ≠ e.st.st.rv := by
          rcases hrv with ⟨_, e2⟩ | ⟨e1, _⟩
          · exact absurd e2 hch
          · rw [e1]; exact rv_succ_ne _
        have hle := h.le
        have hlt : uint.nat e.st.st.rv < uint.nat g.st.st.rv + 1 := by omega
        obtain ⟨hl1, hl2⟩ := canonL_le A _ _ hlt
        generalize hl : canonL A (uint.nat e.st.st.rv) (uint.nat g.st.st.rv + 1) = l at hl1 hl2
        have hmem : l ∈ landingsFull A [] [] (uint.nat e.st.st.rv) := by
          rw [← hl]; exact canonL_mem A [] [] _ _ hlt
        have h' := h.skipTo (l - 1) (by omega)
        have hsrv : uint.nat (skipToL e.st (l - 1)).st.rv = l - 1 := by
          rw [skipToL_rv _ _ (by omega)]; omega
        obtain ⟨_, hrv'⟩ := h'.stepRen i hpre hb
        have hch'' : (mstepL i (skipToL e.st (l - 1)).st).1.rv ≠ (skipToL e.st (l - 1)).st.rv := by
          rcases hrv' with ⟨_, e2⟩ | ⟨e1, _⟩
          · exact absurd e2 hch
          · rw [e1]; exact rv_succ_ne _
        have hcut : CutW A (fun _ => uint.nat g.st.st.rv + 1) (uint.nat (skipToL e.st (l - 1)).st.rv + 1) := by
          rw [hsrv, show l - 1 + 1 = l by omega]
          intro v hv
          have c1 := canonL_cut A _ _ v hlt (Or.inl hv)
          have c2 := canonL_cut A _ _ (v + 1) hlt (Or.inr ⟨v, hv, rfl⟩)
          rw [hl] at c1 c2
          exact ⟨c1, c2⟩
        have hw' := h'.write i hpre hb hch'' hcut
        refine ⟨⟨(kstepL i (skipToL e.st (l - 1))).1, removeAtL e.pend (e.pend.idxOf i)⟩,
          .land _ l hidx (by rw [hat]; exact hch') hmem (by omega) (by rw [hat]; exact .refl _),
          ⟨⟨extR ρ (uint.nat (skipToL e.st (l - 1)).st.rv) (uint.nat g.st.st.rv),
            W ++ [uint.nat (skipToL e.st (l - 1)).st.rv + 1], ?_⟩, hrm, hpw', hpa'⟩⟩
        show HRel A n0 (extR ρ (uint.nat (skipToL e.st (l - 1)).st.rv) (uint.nat g.st.st.rv))
          (W ++ [uint.nat (skipToL e.st (l - 1)).st.rv + 1]) (kstepL i (skipToL e.st (l - 1))).1
          (advanceL g.st (mstepL i g.st.st).1)
        rw [kstepL_write i _ hw]; exact hw'

/-- **The cluster's silent steps are a `settle` of the search.** -/
theorem CRel.reach {A : List Nat} {n0 : Nat} {h0 : HSt} {g g₁ : GCfg} (hs : SReach h0 g g₁) :
    ∀ {e : GCfg}, CRel A n0 e g → ∃ e₁, SettleL A e e₁ ∧ CRel A n0 e₁ g₁ := by
  induction hs with
  | refl => intro e hc; exact ⟨e, .refl _, hc⟩
  | step hs1 _ ih =>
    intro e hc
    obtain ⟨e₁, hs₁, hc₁⟩ := hc.silent hs1
    obtain ⟨e₂, hs₂, hc₂⟩ := ih hc₁
    exact ⟨e₂, hs₁.trans hs₂, hc₂⟩

end go

end k8s_dist
end EtcdGrove
end Perennial
