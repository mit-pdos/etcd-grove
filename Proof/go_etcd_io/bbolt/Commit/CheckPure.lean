/-
The pure facts `freepages`' check needs of a `treeOK` view (U10e of
`notes/bbolt-proof-plan.md`): a root's walk (`pageWalk`) visits each of its own pages
(`ownHas`) once, each a well-formed branch or leaf; the slots of a root's own pages
(`ownSlot`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Model.Mvcc
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- Slot `s` is covered by one of the own pages of the tree from `r`. -/
def ownSlot (P : Pages) (r s : Nat) : Prop :=
  ∃ id pg, ownHas P r id ∧ P !! id = some pg ∧ id ≤ s ∧ s ≤ id + pageOverflow pg

/-- `r` is a root of a tree of the `treeOK` pages `P` (the root bucket's, or a nested bucket's
stored in pages): well-formed, its keys a B+tree's. -/
def ownRootOK (P : Pages) (r : Nat) : Prop :=
  ∃ C : CommitSt, treeOK C ∧ C.pages = P ∧ treeWF P C.hwm r ∧ treeKeys P r none none

/-- `pageWalkF` at a page (`Read/Walk`'s `pageWalkF_succ`). -/
theorem pageWalkF_succ' (P : Pages) (n : Nat) (ids : List Nat) (id : Nat) (pg : List w8)
    (hl : ids.getLast? = some id) (hp : P !! id = some pg) :
    pageWalkF P (n + 1) ids = (id, ids) :: (if pageFlags pg = branchPageFlag
      then (List.range (pageCount pg)).flatMap fun j => pageWalkF P n (ids ++ [branchPgid pg j])
      else []) := by
  simp only [pageWalkF, hl, hp]

/-- The walk below a well-formed page visits well-formed own pages of it. -/
theorem walkF_mem (P : Pages) (hwm : Nat) : ∀ (n : Nat) (ids : List Nat) (id : Nat),
    ids.getLast? = some id → treeWF P hwm id → ∀ e ∈ pageWalkF P n ids,
      treeWF P hwm e.1 ∧ ownHas P id e.1 := by
  intro n
  induction n with
  | zero => intro ids id _ _ e he; simp [pageWalkF] at he
  | succ n ih =>
    intro ids id hl hwf e he
    obtain ⟨pg, hpg, hpt⟩ : ∃ pg, P !! id = some pg ∧ pageTreeWF P hwm pg pg.length := by
      cases hwf with | page _ pg _ _ hpg _ _ hpt => exact ⟨pg, hpg, hpt⟩
    rw [pageWalkF_succ' P n ids id pg hl hpg] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨hwf, ownHas.root id pg hpg⟩
    · split at he
      · rename_i hbr
        obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
        have hj' := List.mem_range.mp hj
        have hch : treeWF P hwm (branchPgid pg j) := by
          cases hpt with
          | leaf _ _ hf _ _ => rw [hf] at hbr; exact absurd hbr (by decide)
          | branch _ _ _ _ hc => exact hc j hj'
        obtain ⟨h1, h2⟩ := ih _ _ (by simp) hch e he
        exact ⟨h1, ownHas.child id pg j e.1 hpg hbr hj' h2⟩
      · simp at he

/-- **A page of a root's walk** is one of its own pages, a well-formed branch or leaf, its
header's id its own, inside the high-water mark. -/
theorem walk_entry (P : Pages) (r : Nat) (h : ownRootOK P r) (k id : Nat) (ids : List Nat)
    (hk : (pageWalk P r)[k]? = some (id, ids)) :
    ∃ pg, P !! id = some pg ∧ ownHas P r id ∧ pageId pg = id ∧ 16 ≤ pg.length ∧
      (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) := by
  obtain ⟨C, -, -, hwf, -⟩ := h
  have hm := List.mem_of_getElem? hk
  obtain ⟨hw, ho⟩ := walkF_mem P C.hwm _ [r] r (by simp) hwf _ hm
  obtain ⟨pg, hpg⟩ : ∃ pg, P !! id = some pg := by
    cases hw with | page _ pg _ _ hpg _ _ _ => exact ⟨pg, hpg⟩
  obtain ⟨-, -, hid, hlen, hfl⟩ := Read.treeWF_page P C.hwm id hw pg hpg
  refine ⟨pg, hpg, ho, hid, ?_, hfl⟩
  have := Nat.le_mul_of_pos_left 4096 (show 0 < 1 + pageOverflow pg by omega)
  omega

-- `pht_chain`/`pht_lt_size` as in `Read/BktOK` (that module imports the read path).
/-- A chain of distinct pages below a well-formed position, as long as its height. -/
private theorem pht_chain' (P : Pages) (hwm : Nat) (pht : Nat → Nat) (hht : pageHts P pht) :
    ∀ (m id : Nat), pht id = m → treeWF P hwm id →
      ∃ L : List Nat, L.Nodup ∧ (∀ x ∈ L, (P !! x).isSome) ∧ L.length = pht id + 1 ∧
        ∀ x ∈ L, pht x ≤ pht id := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro id hm hw
  cases hw with
  | page _ pg _ _ hpg _ _ hpt =>
    cases hpt with
    | leaf _ _ hfl _ _ =>
      refine ⟨[id], by simp, by simp [hpg], ?_, by simp⟩
      simp [(hht id pg hpg).1 hfl]
    | branch _ _ hfl hbwf hch =>
      have hc := (hht id pg hpg).2 hfl 0 hbwf.1
      obtain ⟨L, hnd, hin, hlen, hle⟩ := ih (pht (branchPgid pg 0)) (by omega) _ rfl (hch 0 hbwf.1)
      refine ⟨id :: L, List.nodup_cons.mpr ⟨fun h => by have := hle id h; omega, hnd⟩, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp [hpg]
        · exact hin x hx
      · simp [hlen]; omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · have := hle x hx; omega

/-- **A well-formed position's height is below the page count** (the leaves' fuel suffices). -/
private theorem pht_lt_size' (P : Pages) (hwm : Nat) (pht : Nat → Nat) (hht : pageHts P pht) (id : Nat)
    (hw : treeWF P hwm id) : pht id < P.size + 1 := by
  obtain ⟨L, hnd, hin, hlen, -⟩ := pht_chain' P hwm pht hht _ id rfl hw
  have := List.Nodup.length_le_of_subset hnd
    (fun x hx => (GMap.mem_dom_list P x).mpr (hin x hx))
  rw [← GMap.size_eq_dom_list_length] at this
  omega

/-- A walk from a stack ending at `r` lists every own page of `r` (enough fuel). -/
theorem walkF_cover (P : Pages) (pht : Nat → Nat) (hht : pageHts P pht) {r id : Nat}
    (ho : ownHas P r id) : ∀ (n : Nat) (ids : List Nat), ids.getLast? = some r → pht r < n →
      id ∈ (pageWalkF P n ids).map Prod.fst := by
  induction ho with
  | root r pg hpg =>
    intro n ids hl hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pageWalkF_succ' P m ids r pg hl hpg]
    simp
  | child r pg i id hpg hbr hi _ ih =>
    intro n ids hl hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pageWalkF_succ' P m ids r pg hl hpg, if_pos hbr]
    have hc := (hht r pg hpg).2 hbr i hi
    have := ih m (ids ++ [branchPgid pg i]) (by simp) (by omega)
    simp only [List.map_cons, List.mem_cons, List.map_flatMap]
    right
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, this⟩

/-- **A root's walk visits each page once.** -/
theorem walk_nodup (P : Pages) (r : Nat) (h : ownRootOK P r) :
    ((pageWalk P r).map Prod.fst).Nodup := by
  sorry

/-- **A root's walk visits all its own pages.** -/
theorem walk_cover (P : Pages) (r : Nat) (h : ownRootOK P r) (id : Nat) (ho : ownHas P r id) :
    ∃ (k : Nat) (ids : List Nat), (pageWalk P r)[k]? = some (id, ids) := by
  obtain ⟨C, hok, hCP, hwf, -⟩ := h
  obtain ⟨pht, hht⟩ := hok.1.2.2.2
  rw [hCP] at hht
  have hm := walkF_cover P pht hht ho (P.size + 1) [r] (by simp)
    (pht_lt_size' P C.hwm pht hht r hwf)
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  exact ⟨k, e.2, by rw [show pageWalk P r = pageWalkF P (P.size + 1) [r] from rfl, hk]⟩

/-- Slot `x` is covered by one of the first `i` pages of the walk of `r`. -/
def walkSlot (P : Pages) (r i x : Nat) : Prop :=
  ∃ j < i, ∃ id ids pg, (pageWalk P r)[j]? = some (id, ids) ∧ P !! id = some pg ∧ id ≤ x ∧
    x ≤ id + pageOverflow pg

/-- **The `i`-th page of the walk shares no slot with the earlier ones.** -/
theorem walkSlot_disj (P : Pages) (r : Nat) (h : ownRootOK P r) (i id : Nat) (ids : List Nat)
    (pg : List w8) (hi : (pageWalk P r)[i]? = some (id, ids)) (hpg : P !! id = some pg) (x : Nat)
    (hx : walkSlot P r i x) : ¬ (id ≤ x ∧ x ≤ id + pageOverflow pg) := by
  sorry

/-- **The walk's pages' slots are the own pages' slots.** -/
theorem walkSlot_all (P : Pages) (r : Nat) (h : ownRootOK P r) (x : Nat) :
    walkSlot P r (pageWalk P r).length x ↔ ownSlot P r x := by
  sorry

end pure

end bbolt
end EtcdGrove
end Perennial
