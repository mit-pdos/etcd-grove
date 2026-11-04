/-
`Bucket.spill`'s last step (U9g, `notes/bbolt-proof-plan.md`; pure): **`spillOK` from the root
bucket's written tree**. After the root bucket's spill, its header's root (`X'.rootPage`) is the
root of an `sTree` over the spill's page map (`spP X'`) with the pages `S`; with the slots `D` the
root bucket owned before (base slots, every base slot owned or pending), kept or pending after, the
new slots the tree's or new, `spillOK` follows, given the root shape and the data facts
`treeData_spill'` takes (`hnames`, `hbkts`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktSpec
public import Proof.go_etcd_io.bbolt.Spill.STreeMono
public import Proof.go_etcd_io.bbolt.Spill.TreeDataSpill

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section final
variable [GooseExts]

theorem mem_pagesSlots {P : Pages} {s : Nat} :
    s ∈ pagesSlots P ↔ ∃ id pg, P !! id = some pg ∧ id ≤ s ∧ s < id + (1 + pageOverflow pg) := by
  unfold pagesSlots
  simp only [List.mem_flatMap, List.mem_range']
  constructor
  · rintro ⟨⟨id, pg⟩, hm, i, hi, rfl⟩
    simp only at hi
    exact ⟨id, pg, (GMap.mem_toList P id pg).1 hm, by omega, by omega⟩
  · rintro ⟨id, pg, hp, h1, h2⟩
    exact ⟨(id, pg), (GMap.mem_toList P id pg).2 hp, s - id, by simp only; omega, by omega⟩

/-- A slot of an `sTree`'s pages is a slot of the tree's own pages, and conversely. -/
theorem sTree_slots {P : Pages} {hwm root h : Nat} {S : List Nat}
    (hs : sTree P hwm root none none h S) (s : Nat) :
    s ∈ pgSlots P S ↔ s ∈ pagesSlots (treePages P root) := by
  rw [mem_pagesSlots]
  unfold pgSlots
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hsx⟩
    have ht := (hs.has x).2 hx
    obtain ⟨pg, hpg⟩ := treeHas_page ht
    rw [hpg] at hsx
    simp only [List.mem_range'] at hsx
    obtain ⟨i, hi, rfl⟩ := hsx
    exact ⟨x, pg, by rw [treePages_agree P root x ht]; exact hpg, by omega, by omega⟩
  · rintro ⟨id, pg, hp, h1, h2⟩
    rw [treePages_lookup] at hp
    split at hp
    · rename_i ht
      refine ⟨id, (hs.has id).1 ht, ?_⟩
      rw [hp]; simp only [List.mem_range']
      exact ⟨s - id, by omega, by omega⟩
    · cases hp

/-- A page of the writer's buffers' map is a buffer. -/
theorem bufPages_lookup {X : WX} {id : Nat} {pg : List w8} (h : X.bufPages !! id = some pg) :
    X.t.bufs !! W64 (id : Int) = some pg := by
  unfold WX.bufPages at h
  rw [ofList_lookup_find] at h
  cases hf : (X.t.bufs.toList.map fun e => (e.1.toNat, e.2)).find? (fun e => decide (e.1 = id)) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have he : e.1 = id := by simpa using List.find?_some hf
    obtain ⟨⟨k, bs⟩, hk, rfl⟩ := List.mem_map.1 hm
    simp only at he h
    subst he h
    rw [show W64 (k.toNat : Int) = k by word]
    exact (GMap.mem_toList _ k bs).1 hk

/-- **`spillOK` from the root bucket's written tree** (see the module doc). -/
theorem spillOK_of_root (X X' : WX) (C : CommitSt) (fl fl' : FLPg) (txid : w64)
    (st : List FLStep) (h : Nat) (S D : List Nat)
    (hC : C.pages = X.v.pages) (hv : X'.v.pages = X.v.pages)
    (hmark : X.t.mv.pgid' ≤ X'.t.mv.pgid')
    (hS : sTree (spP X') X'.t.mv.pgid'.toNat X'.rootPage none none h S)
    (hshape : rootShape (treePages (spP X') X'.rootPage) X'.rootPage)
    (htx : X'.t.mv.txid'.toNat < 2 ^ 63)
    (hnames : (treeEntries (treePages (spP X') X'.rootPage) X'.rootPage).map Prod.fst =
      (rootEnts X).map Prod.fst)
    (hbkts : ∀ n v, (n, v) ∈ treeEntries (treePages (spP X') X'.rootPage) X'.rootPage →
      some (bktOfPage (treePages (spP X') X'.rootPage) v) = bktData X n)
    (hfl : fl' = fl.applySteps txid st)
    (hbase : ∀ s ∈ treeSlots C, s ∈ D ∨ s ∈ pendSlots fl')
    (hDdrop : ∀ s ∈ D, s ∈ pgSlots (spP X') S ∨ s ∈ pendSlots fl')
    (hDnew : ∀ s ∈ pgSlots (spP X') S, s ∈ D ∨ newSlot st X.t.mv.pgid'.toNat s)
    (hDbase : ∀ s ∈ D, s ∈ treeSlots C) :
    spillOK X X' C fl fl' txid := by
  have hP : X'.bufPages ∪ C.pages = spP X' := by unfold spP; rw [hC, hv]
  have hpages : (spillC X' C.pages).pages = treePages (spP X') X'.rootPage := by
    show treePages (X'.bufPages ∪ C.pages) X'.rootPage = _; rw [hP]
  have hslots : ∀ s, s ∈ treeSlots (spillC X' C.pages) ↔ s ∈ pgSlots (spP X') S := by
    intro s; unfold treeSlots; rw [hpages]; exact (sTree_slots hS s).symm
  refine ⟨?_, ?_, hv, hmark, ?_, ⟨st, hfl, ?_⟩, ?_⟩
  · exact treeOK_of_sTree (spillC X' C.pages) hS hpages (by rw [hpages]; exact hshape) htx
  · apply treeData_spill'
    · show (treeEntries (spillC X' C.pages).pages X'.rootPage).map Prod.fst = _
      rw [hpages]; exact hnames
    · intro n v hm
      have hm' : (n, v) ∈ treeEntries (treePages (spP X') X'.rootPage) X'.rootPage := by
        rw [← hpages]; exact hm
      rw [show (spillC X' C.pages).pages = _ from hpages]; exact hbkts n v hm'
  · intro s hs hn
    rcases hbase s hs with hd | hp
    · rcases hDdrop s hd with hS' | hp
      · exact absurd ((hslots s).2 hS') hn
      · exact hp
    · exact hp
  · intro s hs
    rcases hDnew s ((hslots s).1 hs) with hd | hn
    · exact Or.inl (hDbase s hd)
    · exact Or.inr hn
  · intro id pg hp
    rw [show (spillC X' C.pages).pages = treePages (X'.bufPages ∪ C.pages) X'.rootPage from rfl]
      at hp
    have hp' := treePages_le _ _ id pg hp
    rcases (GMap.lookup_union_Some_raw _ _ id pg).1 hp' with hb | ⟨-, hc⟩
    · exact Or.inr (bufPages_lookup hb)
    · exact Or.inl hc

end final

end Spill

end bbolt
end EtcdGrove
end Perennial
