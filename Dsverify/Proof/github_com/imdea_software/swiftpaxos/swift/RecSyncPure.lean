/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecSyncPure.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Pure lemmas for `recoveredSync`'s proof (Proof/swift/RecSyncProof.lean): the reports' order
(Go's `SortFunc` by replica is the model's `recAcks`), the highest `cballot`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArith
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumModel

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace swift.rec

/-- A report's pointer with its model report. -/
abbrev Pr := Loc × (Nat × sp.Report)

/-- The replica of the report at `p` (the first pair of `prs` with that pointer). -/
def repOf (prs : List Pr) (p : Loc) : Int :=
  ((prs.find? (fun q => q.1 == p)).map (fun q => (q.2.1 : Int))).getD 0

/-- The comparator's relation: by replica. -/
def RepLt (prs : List Pr) (a b : Loc) : Prop := repOf prs a < repOf prs b

theorem repLt_swo (prs : List Pr) : slices.StrictWeakOrder (RepLt prs) where
  strict_weak_order_irrefl _ := by unfold RepLt; omega
  strict_weak_order_trans _ _ _ h1 h2 := by unfold RepLt at *; omega
  strict_weak_order_equiv := by
    refine ⟨fun x => ?_, fun h => ⟨h.2, h.1⟩, fun {x y z} h1 h2 => ?_⟩
    · unfold RepLt; omega
    · unfold RepLt at *; omega

/-- Pointers determine replicas (the reports' persistent points-to agree). -/
def PtrOk (prs : List Pr) : Prop := ∀ q1 ∈ prs, ∀ q2 ∈ prs, q1.1 = q2.1 → q1.2.1 = q2.2.1

theorem repOf_of_mem {prs : List Pr} (hptr : PtrOk prs) {q : Pr} (hq : q ∈ prs) :
    repOf prs q.1 = q.2.1 := by
  unfold repOf
  cases h : prs.find? (fun q' => q'.1 == q.1) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp h q hq
    simp at this
  | some q' =>
    have hq' := List.mem_of_find?_eq_some h
    have he := List.find?_some h
    simp only [beq_iff_eq] at he
    simp only [Option.map_some, Option.getD_some]
    rw [hptr q' hq' q hq he]

theorem inj_of_nodup_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, hnd, x, y, hx, hy, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd ⟨y, hy', he.symm⟩ hnd.1
    · exact absurd ⟨x, hx', he⟩ hnd.1
    · exact inj_of_nodup_map f hnd.2 hx' hy' he

/-- **The sorted reports**: Go's sorted pointers, with their reports, are the model's
`recAcks` (the stable sort by replica: replicas are distinct). -/
theorem sorted_acks (prs : List Pr) (hptr : PtrOk prs)
    (hnd : ((prs.map Prod.snd).map Prod.fst).Nodup) (ps' : List Loc)
    (hperm : (prs.map Prod.fst).Perm ps')
    (hsorted : ∀ (i j : Nat) (xi xj : Loc), ps'[i]? = some xi → ps'[j]? = some xj → i < j →
      ¬ RepLt prs xj xi) :
    ∃ prs' : List Pr, prs'.Perm prs ∧ prs'.map Prod.fst = ps' ∧
      prs'.map Prod.snd = sp.recAcks (prs.map Prod.snd) := by
  rw [List.map_map] at hnd
  let F : Loc → Option Pr := fun p => prs.find? (fun q => q.1 == p)
  have hF : ∀ q ∈ prs, F q.1 = some q := by
    intro q hq
    cases h : F q.1 with
    | none => exfalso; have := List.find?_eq_none.mp h q hq; simp at this
    | some q' =>
      have hq' := List.mem_of_find?_eq_some h
      have he := List.find?_some h
      simp only [beq_iff_eq] at he
      rw [inj_of_nodup_map (Prod.fst ∘ Prod.snd) hnd hq' hq (hptr q' hq' q hq he)]
  have hid : ∀ l : List Pr, (∀ q ∈ l, q ∈ prs) → (l.map Prod.fst).filterMap F = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro hl
      simp only [List.map_cons, List.filterMap_cons]
      rw [hF a (hl a (by simp)), ih (fun q hq => hl q (by simp [hq]))]
  have hmem : ∀ p ∈ ps', ∃ q ∈ prs, q.1 = p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hperm.symm.subset hp)
    exact ⟨q, hq, rfl⟩
  refine ⟨ps'.filterMap F, ?_, ?_, ?_⟩
  · have := hperm.filterMap F
    rw [hid prs (fun q hq => hq)] at this
    exact this.symm
  · have : ∀ l : List Loc, (∀ p ∈ l, ∃ q ∈ prs, q.1 = p) → (l.filterMap F).map Prod.fst = l := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a l ih =>
        intro hl
        obtain ⟨q, hq, rfl⟩ := hl a (by simp)
        simp only [List.filterMap_cons, hF q hq, List.map_cons]
        rw [ih (fun p hp => hl p (by simp [hp]))]
    exact this ps' hmem
  · -- sorted by replica, with distinct replicas: the model's stable sort
    have hP : (ps'.filterMap F).Perm prs := by
      have := hperm.filterMap F
      rw [hid prs (fun q hq => hq)] at this
      exact this.symm
    have hfst : (ps'.filterMap F).map Prod.fst = ps' := by
      have : ∀ l : List Loc, (∀ p ∈ l, ∃ q ∈ prs, q.1 = p) → (l.filterMap F).map Prod.fst = l := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons a l ih =>
          intro hl
          obtain ⟨q, hq, rfl⟩ := hl a (by simp)
          simp only [List.filterMap_cons, hF q hq, List.map_cons]
          rw [ih (fun p hp => hl p (by simp [hp]))]
      exact this ps' hmem
    generalize ps'.filterMap F = L at hP hfst ⊢
    have hLp : ∀ q ∈ L, q ∈ prs := fun q hq => hP.subset hq
    have hsortL : (L.map Prod.snd).Pairwise (fun a b => decide (a.1 ≤ b.1) = true) := by
      rw [List.pairwise_map, List.pairwise_iff_getElem]
      intro i j hi hj hij
      have hpi : ps'[i]? = some L[i].1 := by
        rw [← hfst, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
      have hpj : ps'[j]? = some L[j].1 := by
        rw [← hfst, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
      have := hsorted i j _ _ hpi hpj hij
      unfold RepLt at this
      rw [repOf_of_mem hptr (hLp _ (List.getElem_mem hi)),
        repOf_of_mem hptr (hLp _ (List.getElem_mem hj))] at this
      simp only [decide_eq_true_eq]; omega
    unfold sp.recAcks
    apply List.Perm.eq_of_pairwise (le := fun a b => decide (a.1 ≤ b.1) = true)
    · intro a b ha hb h1 h2
      simp only [decide_eq_true_eq] at h1 h2
      have ha' : a ∈ prs.map Prod.snd := (hP.map Prod.snd).subset ha
      have hb' : b ∈ prs.map Prod.snd := (List.mergeSort_perm _ _).subset hb
      have hnd2 : ((prs.map Prod.snd).map Prod.fst).Nodup := by rw [List.map_map]; exact hnd
      exact inj_of_nodup_map Prod.fst hnd2 ha' hb' (by omega)
    · exact hsortL
    · exact List.pairwise_mergeSort (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _
    · exact (hP.map Prod.snd).trans (List.mergeSort_perm _ _).symm

/-- The highest `cballot` (Go's from `-1`; the model's from 0: the same for a non-empty list),
invariant by permutation. -/
theorem maxC_eq (prs prs' : List Pr) (hne : prs ≠ []) (hperm : prs'.Perm prs) :
    (prs.map (fun q => (q.2.2.cbal : Int))).foldl max (-1) = (sp.recMaxC (prs'.map Prod.snd) : Int) := by
  have key : ∀ (t : List Nat) (n : Nat),
      (t.map (fun x : Nat => (x : Int))).foldl max (n : Int) = ((t.foldl max n : Nat) : Int) := by
    intro t
    induction t with
    | nil => intro n; rfl
    | cons x t ih =>
      intro n
      simp only [List.map_cons, List.foldl_cons]
      rw [show max (n : Int) (x : Int) = ((max n x : Nat) : Int) by omega, ih]
  have hperm' : (prs'.map Prod.snd |>.map (·.2.cbal)).Perm (prs.map (fun q => q.2.2.cbal)) := by
    rw [List.map_map]; exact hperm.map _
  unfold sp.recMaxC
  rw [hperm'.foldl_eq' (fun x _ y _ z => by simp only [Nat.max_assoc, Nat.max_comm x y]) 0]
  obtain ⟨x, t, rfl⟩ : ∃ x t, prs = x :: t := by
    cases prs with
    | nil => exact absurd rfl hne
    | cons x t => exact ⟨x, t, rfl⟩
  simp only [List.map_cons, List.foldl_cons]
  rw [show max (-1 : Int) (x.2.2.cbal : Int) = ((max 0 x.2.2.cbal : Nat) : Int) by omega]
  have := key (t.map (fun q => q.2.2.cbal)) (max 0 x.2.2.cbal)
  rw [List.map_map] at this
  exact this

end swift.rec

end Perennial.github_com.imdea_software.swiftpaxos
