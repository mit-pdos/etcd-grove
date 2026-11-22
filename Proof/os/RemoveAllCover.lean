/-
Pure facts about the claims `os.RemoveAll.specSubS` takes and gives back (`Spec/os/RemoveAll.lean`:
`ClReach`, `SubCover`, `ClRanked`, `ClsSub`): what its recursion needs (the claims of a directory's
subtree, but the directory's own, cover each entry's subtree, `subCover_pool`) and what its clients
need (the claims it gives back still cover what is left, `SubCover.of_sub`). Lean-first; untrusted.
-/
module

public import Spec.os.RemoveAll
public import Proof.os.RemoveAllLeaf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Fs

theorem ClsSub.refl : ∀ (cl : List Claim), ClsSub cl cl
  | [] => trivial
  | _ :: cl => ⟨rfl, EntsSub.refl _, ClsSub.refl cl⟩

theorem ClsSub.trans : ∀ {a b c : List Claim}, ClsSub a b → ClsSub b c → ClsSub a c
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨k1, s1, h1⟩, ⟨k2, s2, h2⟩ => ⟨k1.trans k2, s1.trans s2, h1.trans h2⟩

theorem ClsSub.length : ∀ {a b : List Claim}, ClsSub a b → a.length = b.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, h⟩ => by simp [h.length]

theorem ClsSub.append : ∀ {a1 b1 a2 b2 : List Claim}, ClsSub a1 b1 → ClsSub a2 b2 →
    ClsSub (a1 ++ a2) (b1 ++ b2)
  | [], [], _, _, _, h2 => h2
  | _ :: _, _ :: _, _, _, ⟨k, s, h⟩, h2 => ⟨k, s, h.append h2⟩

/-- A list `ClsSub` of an append splits as it. -/
theorem ClsSub.split : ∀ {a b1 b2 : List Claim}, ClsSub a (b1 ++ b2) →
    ∃ a1 a2, a = a1 ++ a2 ∧ ClsSub a1 b1 ∧ ClsSub a2 b2
  | a, [], _, h => ⟨[], a, rfl, trivial, h⟩
  | [], _ :: _, _, h => h.elim
  | x :: a, _ :: _, _, ⟨k, s, h⟩ =>
    let ⟨a1, a2, he, h1, h2⟩ := ClsSub.split h
    ⟨x :: a1, a2, by rw [he]; rfl, ⟨k, s, h1⟩, h2⟩

/-- An element of the first list has one of the second on the same names, holding more. -/
theorem ClsSub.mem : ∀ {a b : List Claim}, ClsSub a b → ∀ c' ∈ a,
    ∃ c ∈ b, clKey c = clKey c' ∧ EntsSub c'.2.2.cur c.2.2.cur
  | [], [], _, _, hc => absurd hc List.not_mem_nil
  | x :: a, y :: b, ⟨k, s, h⟩, c', hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨y, List.mem_cons_self, k.symm, s⟩
    · obtain ⟨c, hc, hk, hs⟩ := h.mem c' hc
      exact ⟨c, List.mem_cons_of_mem _ hc, hk, hs⟩

/-- An element of the second list has one of the first on the same names. -/
theorem ClsSub.mem' : ∀ {a b : List Claim}, ClsSub a b → ∀ c ∈ b, ∃ c' ∈ a, clKey c' = clKey c
  | [], [], _, _, hc => absurd hc List.not_mem_nil
  | x :: a, y :: b, ⟨k, _, h⟩, c, hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨x, List.mem_cons_self, k⟩
    · obtain ⟨c', hc', hk⟩ := h.mem' c hc
      exact ⟨c', List.mem_cons_of_mem _ hc', hk⟩

/-- A whole claim of the second list is one of the first's, on the same directory. -/
theorem ClsSub.mem_whole {a b : List Claim} (h : ClsSub a b) {X : Ino} {hX : NamesH}
    (hm : (X, NameSet.except [], hX) ∈ b) : ∃ h', (X, NameSet.except [], h') ∈ a := by
  obtain ⟨c', hc', hk⟩ := h.mem' _ hm
  obtain ⟨X', N', h'⟩ := c'
  simp only [clKey, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  exact ⟨h', hc'⟩

/-- Reach through claims holding fewer entries is reach through the larger ones. -/
theorem ClReach.of_sub {a b : List Claim} (hs : ClsSub a b) {J X : Ino} (hr : ClReach a J X) :
    ClReach b J X := by
  induction hr with
  | refl J => exact .refl J
  | step J J' J'' h c hm he _ ih =>
    obtain ⟨⟨J0, N0, h0⟩, hc0, hk, hsub⟩ := hs.mem _ hm
    simp only [clKey, Prod.mk.injEq] at hk
    obtain ⟨hJ0, hN0⟩ := hk
    rw [hJ0, hN0] at hc0
    exact .step J J' J'' h0 c hc0 (hsub c _ he) ih

/-- Reach through some of the claims is reach through all. -/
theorem ClReach.of_subset {a b : List Claim} (hs : ∀ c ∈ a, c ∈ b) {J X : Ino}
    (hr : ClReach a J X) : ClReach b J X := by
  induction hr with
  | refl J => exact .refl J
  | step J J' J'' h c hm he _ ih => exact .step J J' J'' h c (hs _ hm) he ih

/-- Ranks grow along reach. -/
theorem ClReach.rank_le {cl : List Claim} {rk : Ino → Nat}
    (hrk : ∀ c ∈ cl, ∀ x K, c.2.2.cur !! x = some (.dir K) → rk c.1 < rk K) {J X : Ino}
    (hr : ClReach cl J X) : rk J ≤ rk X := by
  induction hr with
  | refl J => exact Nat.le_refl _
  | step J J' J'' h c hm he _ ih => exact Nat.le_trans (Nat.le_of_lt (hrk _ hm c J' he)) ih

theorem ClRanked.of_sub {a b : List Claim} (hs : ClsSub a b) (h : ClRanked b) : ClRanked a := by
  obtain ⟨rk, hrk⟩ := h
  refine ⟨rk, fun c' hc' x K he => ?_⟩
  obtain ⟨⟨J0, N0, h0⟩, hc0, hk, hsub⟩ := hs.mem _ hc'
  simp only [clKey, Prod.mk.injEq] at hk
  rw [← hk.1]
  exact hrk _ hc0 x K (hsub x _ he)

theorem ClRanked.of_subset {a b : List Claim} (hs : ∀ c ∈ a, c ∈ b) (h : ClRanked b) :
    ClRanked a := by
  obtain ⟨rk, hrk⟩ := h
  exact ⟨rk, fun c hc => hrk c (hs c hc)⟩

/-- **The claims given back still cover what is left** (`os.RemoveAll.specSubS`'s clients): the
entry `e'` is `e` or gone, the claims `cl'` hold some of `cl`'s entries. -/
theorem SubCover.of_sub {cl cl' : List Claim} {e e' : Option Node} (hc : SubCover cl e)
    (hs : ClsSub cl' cl) (he : ∀ n, e' = some n → e = some n) : SubCover cl' e' := by
  intro J hJ X hr
  obtain ⟨hX, hm⟩ := hc J (he _ hJ) X (hr.of_sub hs)
  exact hs.mem_whole hm

/-- A directory's entries `e'`, some of `e`'s, whose names are files or nothing, as an entry. -/
theorem SubCover.not_dir {cl : List Claim} {e : Option Node} (he : ∀ J, e ≠ some (.dir J)) :
    SubCover cl e := fun J hJ => absurd hJ (he J)

/-- **The pool of `RemoveAll`'s recursion covers an entry of the directory it removes** (`J`, whose
whole claim is taken out of `cl = l1 ++ [J's] ++ l2`; the pool holds some of the entries of the rest):
the directories under `K`, an entry of `J`, are not `J` (`ClRanked`), so their claims are in the pool. -/
theorem subCover_pool {l1 l2 pool : List Claim} {J K : Ino} {hJ : NamesH} {c : GoString}
    (hcov : SubCover (l1 ++ (J, NameSet.except [], hJ) :: l2) (some (.dir J)))
    (hrk : ClRanked (l1 ++ (J, NameSet.except [], hJ) :: l2))
    (hs : ClsSub pool (l1 ++ l2)) (hK : hJ.cur !! c = some (.dir K)) :
    SubCover pool (some (.dir K)) := by
  intro K' hK' X hr
  cases hK'
  have hsub : ∀ x ∈ l1 ++ l2, x ∈ l1 ++ (J, NameSet.except [], hJ) :: l2 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
  have hr' : ClReach (l1 ++ (J, NameSet.except [], hJ) :: l2) K X := (hr.of_sub hs).of_subset hsub
  have hJm : (J, NameSet.except [], hJ) ∈ l1 ++ (J, NameSet.except [], hJ) :: l2 :=
    List.mem_append_right _ List.mem_cons_self
  obtain ⟨hX, hm⟩ := hcov J rfl X (.step J K X hJ c hJm hK hr')
  obtain ⟨rk, hrkf⟩ := hrk
  have hlt : rk J < rk K := hrkf _ hJm c K hK
  have hle : rk K ≤ rk X := hr'.rank_le hrkf
  have hne : X ≠ J := fun h => by subst h; omega
  have hm' : (X, NameSet.except [], hX) ∈ l1 ++ l2 := by
    rcases List.mem_append.1 hm with hm | hm
    · exact List.mem_append_left _ hm
    · rcases List.mem_cons.1 hm with hm | hm
      · simp only [Prod.mk.injEq] at hm; exact absurd hm.1 hne
      · exact List.mem_append_right _ hm
  exact hs.mem_whole hm'

/-- The rank of the claims of a removal's pool (`l1 ++ l2` of `l1 ++ [J's] ++ l2`). -/
theorem ClRanked.pool {l1 l2 pool : List Claim} {x : Claim} (hrk : ClRanked (l1 ++ x :: l2))
    (hs : ClsSub pool (l1 ++ l2)) : ClRanked pool := by
  refine ClRanked.of_sub hs (ClRanked.of_subset (fun c hc => ?_) hrk)
  rcases List.mem_append.1 hc with hc | hc
  · exact List.mem_append_left _ hc
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hc)

end EtcdGrove
end Perennial

end
