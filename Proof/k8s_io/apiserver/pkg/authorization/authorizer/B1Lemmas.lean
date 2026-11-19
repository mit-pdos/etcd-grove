/-
Lean-first (no Rocq counterpart).

Pure lemmas for the proofs of batch 1 of the authorizer package: what `sets.New`, `Insert` and
`Delete` of decision words do to a set described by a `PD` (`setIs`).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open sets

section pure
variable [GooseExts]

theorem insertAll_isSome (s : GMap w64 Elem) (ks : List w64) (k : w64) :
    (insertAll s ks !! k).isSome = ((s !! k).isSome || decide (k ∈ ks)) := by
  induction ks generalizing s with
  | nil => simp
  | cons k' ks ih =>
    rw [insertAll_cons, ih]
    simp only [GMap.lookup_insert_eq_iff, List.mem_cons]
    by_cases h : k' = k
    · subst h; simp
    · simp [h, Ne.symm h]

theorem deleteAll_isSome (s : GMap w64 Elem) (ks : List w64) (k : w64) :
    (deleteAll s ks !! k).isSome = ((s !! k).isSome && !decide (k ∈ ks)) := by
  induction ks generalizing s with
  | nil => simp
  | cons k' ks ih =>
    rw [deleteAll_cons, ih]
    simp only [GMap.lookup_delete_iff, List.mem_cons]
    by_cases h : k' = k
    · subst h; simp
    · simp [h, Ne.symm h]

theorem PD.has_or (p q : PD) (k : w64) : (p.or q).has k = (p.has k || q.has k) := by
  obtain ⟨a1, a2, a3⟩ := p
  obtain ⟨b1, b2, b3⟩ := q
  simp only [PD.has, PD.or]
  generalize decide (k = W64 0) = x
  generalize decide (k = W64 1) = y
  generalize decide (k = W64 2) = z
  revert a1 a2 a3 b1 b2 b3 x y z
  decide

/-- The decision words `ks` as a `PD`. -/
def PD.ofList (ks : List w64) : PD :=
  ⟨decide (W64 0 ∈ ks), decide (W64 1 ∈ ks), decide (W64 2 ∈ ks)⟩

/-- A list of valid decision words describes its `PD`. -/
theorem PD.ofList_has (ks : List w64) (hks : ∀ k ∈ ks, k = W64 0 ∨ k = W64 1 ∨ k = W64 2)
    (k : w64) : (PD.ofList ks).has k = decide (k ∈ ks) := by
  simp only [PD.has, PD.ofList]
  by_cases h0 : k = W64 0
  · subst h0; simp
  by_cases h1 : k = W64 1
  · subst h1; simp
  by_cases h2 : k = W64 2
  · subst h2; simp
  have : k ∉ ks := fun hk => by rcases hks k hk with h | h | h <;> contradiction
  simp only [decide_eq_false h0, decide_eq_false h1, decide_eq_false h2, decide_eq_false this,
    Bool.false_and, Bool.or_false]

theorem setIs_insertAll (s : GMap w64 Elem) (p : PD) (ks : List w64) (h : setIs s p)
    (hks : ∀ k ∈ ks, k = W64 0 ∨ k = W64 1 ∨ k = W64 2) :
    setIs (insertAll s ks) (p.or (PD.ofList ks)) := by
  intro k
  rw [insertAll_isSome, h k, PD.has_or, PD.ofList_has ks hks]

theorem setIs_new (ks : List w64) (hks : ∀ k ∈ ks, k = W64 0 ∨ k = W64 1 ∨ k = W64 2) :
    setIs (insertAll ∅ ks) (PD.ofList ks) := by
  intro k
  rw [insertAll_isSome, PD.ofList_has ks hks]
  simp

/-- The union with a set read from another set. -/
theorem setIs_insertAll_set (s t : GMap w64 Elem) (p q : PD) (ks : List w64) (h : setIs s p)
    (ht : setIs t q) (hks : ∀ k, k ∈ ks ↔ (t !! k).isSome) :
    setIs (insertAll s ks) (p.or q) := by
  intro k
  rw [insertAll_isSome, h k, PD.has_or, ← ht k]
  congr 1
  by_cases hk : k ∈ ks
  · simp [hk, (hks k).mp hk]
  · have : ¬ (t !! k).isSome := fun h' => hk ((hks k).mpr h')
    simp [hk, this]

theorem setIs_deleteNoOpinion (s : GMap w64 Elem) (p : PD) (h : setIs s p) :
    setIs (deleteAll s [W64 2]) ⟨p.deny, p.allow, false⟩ := by
  intro k
  rw [deleteAll_isSome, h k]
  cases p
  simp only [PD.has, List.mem_singleton]
  by_cases h0 : k = W64 0
  · subst h0; simp
  by_cases h1 : k = W64 1
  · subst h1; simp
  by_cases h2 : k = W64 2
  · subst h2; simp
  simp only [decide_eq_false h0, decide_eq_false h1, decide_eq_false h2, Bool.false_and,
    Bool.or_false]

theorem setIs_congr {s : GMap w64 Elem} {p q : PD} (h : setIs s p) (hpq : p = q) : setIs s q :=
  hpq ▸ h

/-- `len(s) > 0` of a slice holding `vs`. -/
theorem len_pos_iff {V : Type} (vs : List V) (len : w64) (h1 : vs.length = sint.nat len)
    (h2 : 0 ≤ sint.Z len) : decide (sint.Z (W64 0) < sint.Z len) = !vs.isEmpty := by
  have h0 : sint.Z (W64 0) = 0 := by decide
  have hn : sint.nat len = (sint.Z len).toNat := rfl
  rw [h0]
  cases vs with
  | nil => simp at h1; simp; omega
  | cons v vs => simp at h1; simp; omega

/-- A set of decisions has at most three items (Deny, Allow, NoOpinion), well within
`sets.List'.specW`'s bound (`slices.Sort`'s `2^62`). -/
theorem setIs_size_le_b1 {s : GMap w64 Elem} {p : PD} (h : setIs s p) : GMap.size s ≤ 2 ^ 62 := by
  have hnd : ([W64 0, W64 1, W64 2].filter (fun k => p.has k)).Nodup :=
    List.Pairwise.sublist (List.filter_sublist) (by decide)
  rw [GMap.size_eq_length s _ hnd (fun k => by
    rw [h k, List.mem_filter]
    constructor
    · exact fun h' => h'.2
    · intro h'
      refine ⟨?_, h'⟩
      rcases PD.has_valid p k h' with rfl | rfl | rfl <;> simp)]
  have := List.length_filter_le (fun k => p.has k) [W64 0, W64 1, W64 2]
  simp only [List.length_cons, List.length_nil] at this
  omega

end pure

section defs
open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- A conditions map decision's Deny and Allow conditions' slices (read-only). -/
theorem isDecision_cmap_slices (d : ConditionsAwareDecision) (dn no al : List GoInterface) :
    isDecision (GF := GF) d (.cmap dn no al) ⊢
      d.conditionsMap'.denyConditions' ↦*□ dn ∗ d.conditionsMap'.allowConditions' ↦*□ al := by
  iintro #Hd
  ihave #Hcm := isDecision_cmap d dn no al $$ Hd
  unfold isConditionsMap condsOk
  icases Hcm with ⟨⟨#Hdn, -⟩, -, ⟨#Hal, -⟩⟩
  iframe Hdn Hal

end defs

end authorizer
end EtcdGrove
end Perennial
