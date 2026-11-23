/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumLemmas.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Lemmas of the quorum predicates (`QuorumSpecs.lean`): a leader's list's size and growth, access
to one leader's list in a quorum set, and the pure facts of `addL` and of the quorum maps.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumMapsDefs
@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.quorum

/-! ## Pure facts -/

theorem addL_append (L : Nat → List (List Nat)) (E1 E2 : List (List Nat)) :
    addL (addL L E1) E2 = addL L (E1 ++ E2) := by
  funext l; simp [addL, List.filter_append]

/-- `L` with leader `l`'s list replaced by `Q`. -/
def updL (L : Nat → List (List Nat)) (l : Nat) (Q : List (List Nat)) : Nat → List (List Nat) :=
  fun l' => if l' = l then Q else L l'

theorem addL_nil (L : Nat → List (List Nat)) : addL L [] = L := by
  funext l; simp [addL]

/-- The domain of a leader's list map: the `qid`s below `n`. -/
theorem lqs_size (m : GMap w32 Loc) (n : Nat) (hn : n < 2 ^ 31)
    (h : ∀ k : w32, (m !! k).isSome ↔ ∃ i < n, k = w32n i) : GMap.size m = n := by
  rw [GMap.size_eq_length m ((List.range n).map w32n)]
  · simp
  · apply nodup_map_w32n _ List.nodup_range
    intro x hx; simp at hx; omega
  · intro k; rw [h k]; simp [eq_comm]

theorem qRepr_insert (m : GMap w32 Unit) (s : List Nat) (j : Nat) (h : qRepr m s) :
    qRepr (<[w32n j := ()]> m) (s ++ [j]) := by
  intro k
  by_cases hk : w32n j = k
  · subst hk; simp
  · rw [GMap.lookup_insert_ne _ _ hk, h k]
    simp [Ne.symm hk]

theorem qRepr_delete (m : GMap w32 Unit) (s : List Nat) (j : Nat) (h : qRepr m (s ++ [j]))
    (hj : ∀ x ∈ s, w32n x ≠ w32n j) : qRepr (GMap.delete (w32n j) m) s := by
  intro k
  by_cases hk : w32n j = k
  · subst hk
    simp only [GMap.lookup_delete]
    rw [if_neg]
    simp only [List.mem_map, not_exists, not_and]
    intro x hx; exact hj x hx
  · rw [GMap.lookup_delete_ne _ hk, h k]
    simp [Ne.symm hk]

section iris
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics]

/-- A leader's list grows by one quorum, at `qid = |Q|`. -/
theorem lqsOwn_snoc (p : Loc) (m : GMap w32 Loc) (Q : List (List Nat)) (nq : Loc) (s : List Nat)
    (hQ : Q.length + 1 < 2 ^ 31) (hdom : ∀ k : w32, (m !! k).isSome ↔ ∃ i < Q.length, k = w32n i) :
    p ↦$ (<[w32n Q.length := nq]> m) ∗ qOwn nq DFrac.discard s ∗
      ([∗list] i ↦ s ∈ Q, ∃ ql, ⌜m !! w32n i = some ql⌝ ∗ qOwn ql DFrac.discard s) ⊢
    lqsOwn p (DFrac.own 1) (Q ++ [s]) := by
  iintro ⟨Hm, #Hnq, HQ⟩
  unfold lqsOwn
  iexists _
  iframe Hm
  isplitr
  · ipureintro
    refine ⟨by simpa using hQ, fun k => ?_⟩
    by_cases hk : w32n Q.length = k
    · subst hk; simp only [GMap.lookup_insert, Option.isSome_some, List.length_append,
        List.length_singleton, true_iff]
      exact ⟨Q.length, by omega, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ hk, hdom k]
      simp only [List.length_append, List.length_singleton]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨i, ?_, rfl⟩
        rcases Nat.lt_or_ge i Q.length with h | h
        · exact h
        · exfalso; apply hk; congr 1; omega
  have hmono : ([∗list] i ↦ s ∈ Q, ∃ ql, ⌜m !! w32n i = some ql⌝ ∗ qOwn ql DFrac.discard s) ⊢
      ([∗list] i ↦ s ∈ Q, ∃ ql, ⌜(<[w32n Q.length := nq]> m) !! w32n i = some ql⌝ ∗
        qOwn ql DFrac.discard s : IProp netDistGF) := by
    apply BI.BigSepL.bigSepL_mono
    intro k x hk
    have hkl : k < Q.length := (List.getElem?_eq_some_iff.mp hk).1
    iintro ⟨%ql, %Hql, Hq⟩
    iexists ql
    iframe Hq
    ipureintro
    rw [GMap.lookup_insert_ne]
    · exact Hql
    · intro h; have := w32n_inj _ _ (by omega) (by omega) h; omega
  iapply BI.BigSepL.bigSepL_snoc.2
  isplitl [HQ]
  · iapply hmono $$ HQ
  · iexists nq
    iframe Hnq
    ipureintro; simp

theorem lqsOwn_persist (p : Loc) (Q : List (List Nat)) :
    lqsOwn p (DFrac.own 1) Q ⊢ |==> lqsOwn p DFrac.discard Q := by
  unfold lqsOwn
  iintro ⟨%m, Hm, %Hdom, Hbig⟩
  imod (ownMap_persist (K := w32) (V := Loc)) $$ Hm with #Hm
  imodintro
  iexists m
  iframe Hm Hbig
  ipureintro; exact Hdom

/-- A quorum set is made read only. -/
theorem qsOwn_persist (qs : Loc) (N : Nat) (L : Nat → List (List Nat)) :
    qsOwn qs N L (DFrac.own 1) ⊢ |==> qsOwn qs N L DFrac.discard := by
  unfold qsOwn
  iintro ⟨%m, #Hm, %Hdom, Hbig⟩
  have hmono : ([∗list] l ∈ List.range N, ∃ p, ⌜m !! w32n l = some p⌝ ∗
        lqsOwn p (DFrac.own 1) (L l)) ⊢
      ([∗list] l ∈ List.range N, |==> ∃ p, ⌜m !! w32n l = some p⌝ ∗
        lqsOwn p DFrac.discard (L l) : IProp netDistGF) := by
    apply BI.BigSepL.bigSepL_mono
    intro k x _
    iintro ⟨%p, %Hp, Hl⟩
    imod lqsOwn_persist $$ Hl with Hl
    imodintro
    iexists p
    iframe Hl
    ipureintro; exact Hp
  ihave Hbig := hmono $$ Hbig
  imod (Iris.BigSepL.bigSepL_bupd _ _) $$ Hbig with Hbig
  imodintro
  iexists m
  iframe Hm Hbig
  ipureintro; exact Hdom

/-- A quorum set depends only on the lists of the leaders below `N`. -/
theorem qsOwn_congr (qs : Loc) (N : Nat) (L1 L2 : Nat → List (List Nat)) (dq : DFrac)
    (h : ∀ l < N, L1 l = L2 l) : qsOwn qs N L1 dq ⊢ qsOwn qs N L2 dq := by
  unfold qsOwn
  iintro ⟨%m, #Hm, %Hdom, Hbig⟩
  iexists m
  iframe Hm
  isplitr
  · ipureintro; exact Hdom
  have hmono : ([∗list] l ∈ List.range N, ∃ p, ⌜m !! w32n l = some p⌝ ∗ lqsOwn p dq (L1 l)) ⊢
      ([∗list] l ∈ List.range N, ∃ p, ⌜m !! w32n l = some p⌝ ∗ lqsOwn p dq (L2 l) :
        IProp netDistGF) := by
    apply BI.BigSepL.bigSepL_mono
    intro k x hk
    have hx : x < N := by
      have := List.getElem?_eq_some_iff.mp hk; simp at this; omega
    rw [h x hx]
  iapply hmono $$ Hbig

/-- One leader's list of a quorum set, and the set with that list replaced. -/
theorem qsOwn_acc (qs : Loc) (N : Nat) (L : Nat → List (List Nat)) (dq : DFrac) (l : Nat)
    (hl : l < N) :
    qsOwn qs N L dq ⊢ ∃ (m : GMap w32 Loc) (p : Loc), qs ↦$□ m ∗ ⌜m !! w32n l = some p⌝ ∗
      ⌜∀ k : w32, (m !! k).isSome ↔ ∃ l < N, k = w32n l⌝ ∗
      lqsOwn p dq (L l) ∗ (∀ Q, lqsOwn p dq Q -∗ qsOwn qs N (updL L l Q) dq) := by
  unfold qsOwn
  iintro ⟨%m, #Hm, %Hdom, Hbig⟩
  have hget : (List.range N)[l]? = some l := by simp [hl]
  icases (BI.BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ l' => iprop(∃ p, ⌜m !! w32n l' = some p⌝ ∗
      lqsOwn p dq (L l'))) hget) $$ Hbig with ⟨⟨%p, %Hp, Hl⟩, Hclose⟩
  iexists m, p
  iframe Hm Hl
  isplitr
  · ipureintro; exact Hp
  isplitr
  · ipureintro; exact Hdom
  iintro %Q HQ
  iexists m
  iframe Hm
  isplitr
  · ipureintro; exact Hdom
  iapply Hclose $$ %(fun _ l' => iprop(∃ p, ⌜m !! w32n l' = some p⌝ ∗ lqsOwn p dq (updL L l Q l')))
  · imodintro
    iintro %k %y %Hk %Hne ⟨%p', %Hp', H⟩
    have : y = k := by
      have := List.getElem?_eq_some_iff.mp Hk
      simp at this; omega
    subst this
    iexists p'
    unfold updL
    rw [if_neg Hne]
    iframe H
    ipureintro; exact Hp'
  · iexists p
    unfold updL
    rw [if_pos rfl]
    iframe HQ
    ipureintro; exact Hp

end iris

end replica.quorum

end Perennial.github_com.imdea_software.swiftpaxos

end
