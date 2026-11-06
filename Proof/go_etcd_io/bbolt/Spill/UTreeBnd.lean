/-
The spill's pure tree facts (U9f, `notes/bbolt-proof-plan.md`): **an unspilled tree within looser
bounds** (`uTree_bnd`), what the parent's rebuild after a child's spill needs (the entry before
the child's has its upper bound raised to the first piece's key), and the nodes of an unspilled
tree are unspilled (`uTree_N_unspilled`) and its base pages among its slots (`uTree_F_D`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame
public import Proof.go_etcd_io.bbolt.Spill.STreeMono

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section bnd
variable [GooseExts]

theorem uNode_bnd {X : WX} {bl n : Loc} {r : NRec} {lo hi lo' hi' : Option (List w8)}
    (hb : bndIn (lo, hi) (lo', hi')) (hu : uNode X bl n r lo hi) : uNode X bl n r lo' hi' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hent, h8⟩ := hu
  refine ⟨h1, h2, h3, h4, h5, h6, fun w hw => ?_, h8⟩
  obtain ⟨hk, hl, hm⟩ := hent w hw
  exact ⟨keyIn_bndIn hb w.key hk, hl, hm⟩

/-- The upper bound of a child within looser bounds of its parent. -/
theorem bndIn_childHi {k : List w8} {hi hi' : Option (List w8)}
    (hb : ∀ y, hi' = some y → ∃ x, hi = some x ∧ ¬ go.GoStringLt y x)
    (ks : Nat → List w8) (n i : Nat) :
    bndIn (some k, childHi hi ks n i) (some k, childHi hi' ks n i) := by
  refine ⟨fun y hy => ⟨y, hy, rk_le_refl y⟩, fun y hy => ?_⟩
  unfold childHi at hy ⊢
  by_cases hin : i + 1 < n
  · rw [if_pos hin] at hy ⊢; exact ⟨y, hy, rk_le_refl y⟩
  · rw [if_neg hin] at hy ⊢; exact hb y hy

theorem fTree_bnd {P : Pages} {hwm id : Nat} {k : List w8} {hi hi' : Option (List w8)} {h : Nat}
    {S : List Nat} {E : List El} (hb : ∀ y, hi' = some y → ∃ x, hi = some x ∧ ¬ go.GoStringLt y x)
    (hf : fTree P hwm id k hi h S E) : fTree P hwm id k hi' h S E :=
  ⟨sTree_bnd (lo := some k) (hi := hi) (lo' := some k) (hi' := hi')
    ⟨fun y hy => ⟨y, hy, rk_le_refl y⟩, hb⟩ hf.1, hf.2⟩

/-- **An unspilled tree within looser bounds.** -/
theorem uTree_bnd {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm n lo hi h F D N E) :
    ∀ lo' hi', bndIn (lo, hi) (lo', hi') → uTree X bl P hwm n lo' hi' h F D N E :=
  uTree.rec (X := X) (bl := bl) (P := P) (hwm := hwm)
    (motive_1 := fun n lo hi h F D N E _ => ∀ lo' hi', bndIn (lo, hi) (lo', hi') →
      uTree X bl P hwm n lo' hi' h F D N E)
    (motive_2 := fun n lo hi ws cs h i w e _ => ∀ lo' hi', bndIn (lo, hi) (lo', hi') →
      uEnt X bl P hwm n lo' hi' ws cs h i w e)
    (fun n r lo hi Sb hr hun hleaf hcs hbv hb0 lo' hi' hb =>
      uTree.leaf n r lo' hi' Sb hr (uNode_bnd hb hun) hleaf hcs hbv hb0)
    (fun n r lo hi h es hr hun hleaf h2 hlen _ hchnd hcs hcsnd hNnd hpg0 ih lo' hi' hb =>
      uTree.branch n r lo' hi' h es hr (uNode_bnd hb hun) hleaf h2 hlen
        (fun i w e hw he => ih i w e hw he lo' hi' hb) hchnd hcs hcsnd hNnd hpg0)
    (fun n lo hi ws cs h i w c rc F D N E hc hrc hpar hpg hkey hk' hne _ ih lo' hi' hb =>
      uEnt.child n lo' hi' ws cs h i w c rc F D N E hc hrc hpar hpg hkey hk' hne
        (ih _ _ (bndIn_child hb (wKey ws) ws.length i)))
    (fun n lo hi ws cs h i w S E hf lo' hi' hb =>
      uEnt.fin n lo' hi' ws cs h i w S E (fTree_bnd (fun y hy => by
        have H := (bndIn_child hb (wKey ws) ws.length i).2 y hy
        exact H) hf))
    hu

/-- An entry within looser bounds. -/
theorem uEnt_bnd {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi lo' hi' : Option (List w8)} {ws : List WEntry} {cs : List Loc} {h i : Nat}
    {w : WEntry} {e : UE} (hb : bndIn (lo, hi) (lo', hi'))
    (he : uEnt X bl P hwm n lo hi ws cs h i w e) : uEnt X bl P hwm n lo' hi' ws cs h i w e := by
  cases he with
  | child _ _ _ _ _ _ _ _ c rc F D N E hc hrc hpar hpg hkey hk' hne hut =>
    exact uEnt.child _ _ _ _ _ _ _ _ c rc F D N E hc hrc hpar hpg hkey hk' hne
      (uTree_bnd hut _ _ (bndIn_child hb (wKey ws) ws.length i))
  | fin _ _ _ _ _ _ _ _ S E hf =>
    exact uEnt.fin _ _ _ _ _ _ _ _ S E
      (fTree_bnd (fun y hy => (bndIn_child hb (wKey ws) ws.length i).2 y hy) hf)

/-! ## The nodes and the base pages -/

/-- **The nodes of an unspilled tree are unspilled nodes** of its bucket. -/
theorem uTree_N_unspilled {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm n lo hi h F D N E) :
    ∀ l ∈ N, ∃ r, X.node bl l = some r ∧ r.nv.spilled' = false :=
  uTree.rec (X := X) (bl := bl) (P := P) (hwm := hwm)
    (motive_1 := fun _ _ _ _ _ _ N _ _ => ∀ l ∈ N, ∃ r, X.node bl l = some r ∧ r.nv.spilled' = false)
    (motive_2 := fun _ _ _ _ _ _ _ _ e _ =>
      ∀ l ∈ e.N, ∃ r, X.node bl l = some r ∧ r.nv.spilled' = false)
    (fun n r _ _ _ hr hun _ _ _ _ l hl => by
      rw [List.mem_singleton] at hl; subst hl; exact ⟨r, hr, hun.2.2.1⟩)
    (fun n r _ _ _ es hr hun _ _ _ _ _ _ _ _ _ ih l hl => by
      rcases List.mem_cons.1 hl with rfl | hl
      · exact ⟨r, hr, hun.2.2.1⟩
      · obtain ⟨e, he, hle⟩ := List.mem_flatMap.1 hl
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
        have hlen : i < es.length := (List.getElem?_eq_some_iff.1 hi).1
        obtain ⟨w, hw⟩ : ∃ w, r.ws[i]? = some w := by
          rename_i hlen' _ _ _ _ _ _
          exact ⟨r.ws[i]'(by omega), List.getElem?_eq_getElem _⟩
        exact ih i w e hw hi l hle)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ _ _ _ _ l hl => by simp at hl)
    hu

/-- A node not among the nodes of `X` (fresh) is no node of an unspilled tree, nor spilled. -/
theorem fresh_not_N {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm n lo hi h F D N E) {l : Loc} (hl : X.node bl l = none) :
    l ∉ N ∧ ¬ spilledN X bl l := by
  refine ⟨fun hm => ?_, fun ⟨_, rc, hrc, _⟩ => by rw [hl] at hrc; cases hrc⟩
  obtain ⟨r, hr, -⟩ := uTree_N_unspilled hu l hm
  rw [hl] at hr; cases hr

theorem ownF_ownSl (v : View) (p : w64) : ∀ x ∈ ownF p, x ∈ ownSl v p := by
  intro x hx
  unfold ownF at hx; unfold ownSl
  split at hx
  · simp at hx
  · rw [if_neg (by assumption)]
    rw [List.mem_singleton] at hx; subst hx
    exact mem_pgSlots_self (List.mem_singleton_self _)

/-- **An unspilled tree's base pages are among its slots.** -/
theorem uTree_F_D {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm n lo hi h F D N E) : ∀ x ∈ F, x ∈ D :=
  uTree.rec (X := X) (bl := bl) (P := P) (hwm := hwm)
    (motive_1 := fun _ _ _ _ F D _ _ _ => ∀ x ∈ F, x ∈ D)
    (motive_2 := fun _ _ _ _ _ _ _ _ e _ => ∀ x ∈ e.F, x ∈ e.D)
    (fun n r _ _ _ _ _ _ _ _ _ x hx => List.mem_append_left _ (ownF_ownSl _ _ x hx))
    (fun n r _ _ _ es hr _ _ _ hlen _ _ _ _ _ _ ih x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact List.mem_append_left _ (ownF_ownSl _ _ x hx)
      · obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 hx
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
        have hlt : i < r.ws.length := by
          have := (List.getElem?_eq_some_iff.1 hi).1; omega
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he,
          ih i (r.ws[i]'hlt) e (List.getElem?_eq_getElem _) hi x hxe⟩))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ _ _ _ _ x hx => by simp at hx)
    hu

end bnd

end Spill

end bbolt
end EtcdGrove
end Perennial
