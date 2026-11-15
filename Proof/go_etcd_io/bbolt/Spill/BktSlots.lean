/-
`Bucket.spill` (U9o, `notes/bbolt-proof-plan.md`): **the starting freelist facts of the root
spill's trees**. An unspilled tree's base pages (`uTree`'s `F`) are view pages below `2 ^ 62`
(`uTree_F_view`); at the start of the spill (no page cached: `txClean`'s `pm = ∅`) view pages can
be freed by the writer (`spFree`: the base view's allocations are before the writer, `mvccView`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTreeBnd

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section slots
variable [GooseExts]

theorem ownF_view {v : View} {p : w64} (h : ownPg v p) :
    ∀ x ∈ ownF p, (v.pages !! x).isSome ∧ x < 2 ^ 62 := by
  intro x hx
  unfold ownF at hx
  split at hx
  · simp at hx
  · rename_i h0
    rw [List.mem_singleton] at hx; subst hx
    obtain ⟨pg, hpg, -, -, -, -, hb⟩ := h h0
    exact ⟨by rw [hpg]; rfl, by omega⟩

/-- **An unspilled tree's base pages are view pages below `2 ^ 62`.** -/
theorem uTree_F_view {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm n lo hi h F D N E) :
    ∀ x ∈ F, (X.v.pages !! x).isSome ∧ x < 2 ^ 62 :=
  uTree.rec (X := X) (bl := bl) (P := P) (hwm := hwm)
    (motive_1 := fun _ _ _ _ F _ _ _ _ => ∀ x ∈ F, (X.v.pages !! x).isSome ∧ x < 2 ^ 62)
    (motive_2 := fun _ _ _ _ _ _ _ _ e _ => ∀ x ∈ e.F, (X.v.pages !! x).isSome ∧ x < 2 ^ 62)
    (fun _ _ _ _ _ _ huN _ _ _ _ x hx => ownF_view huN.2.2.2.2.2.2.2 x hx)
    (fun n r _ _ _ es _ huN _ _ hlen _ _ _ _ _ _ ih x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact ownF_view huN.2.2.2.2.2.2.2 x hx
      · obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 hx
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
        have hlt : i < r.ws.length := by
          have := (List.getElem?_eq_some_iff.1 hi).1; omega
        exact ih i (r.ws[i]'hlt) e (List.getElem?_eq_getElem _) hi x hxe)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ _ _ _ _ x hx => by simp at hx)
    hu

/-- **View pages can be freed by the writer at the start of the spill** (no page cached; the base
view's allocations before the writer's txid). -/
theorem spFree_start {X : WX} {fl : FLPg} {F : List Nat} (hc : txClean X) (hmv : mvccView fl X.v)
    (hF : ∀ x ∈ F, (X.v.pages !! x).isSome ∧ x < 2 ^ 62) : spFree X fl X.t.mv.txid' F := by
  intro id hid
  have hpm : X.t.pm = ∅ := hc.2.1.1
  have htx : X.v.txid + 1 = X.t.mv.txid'.toNat := hc.2.2.2.1
  refine ⟨by rw [hpm]; rfl, ?_⟩
  obtain ⟨hs, -⟩ := hF id hid
  obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.1 hs
  cases ha : fl.allocs !! W64 (id : Int) with
  | none =>
    simp only [Option.getD_none]
    intro h0; rw [← h0] at htx; simp at htx
  | some a =>
    simp only [Option.getD_some]
    have := hmv.1 id pg hpg a ha
    intro he; rw [he] at this; omega

end slots

end Spill

end bbolt
end EtcdGrove
end Perennial
