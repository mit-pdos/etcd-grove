/-
`node.spill` after its children's loop (U9w2, `notes/bbolt-proof-plan.md`; pure): **`n`'s entries'
global families** (`tail_glob`), for `pcInv_init`: per entry `m` of `n` (record `r'` after the
children's loop), its slots `Sb m` and (branch) leaf elements `Eb m`: a leaf's nested buckets'
values (`uTree.leaf`), a branch's finished subtrees (every entry is `fin` after the children's
loop: its children all spilled, `uEnt_fin_of_spilled`); the tree's slots and leaf elements as
the families' concatenations, with the children's loop's bookkeeping.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv
public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section glob

/-- A list's `flatMap` as a family over its indices. -/
theorem flatMap_eq_range {α β : Type} (es : List α) (g : α → List β) (f : Nat → List β)
    (h : ∀ m e, es[m]? = some e → g e = f m) :
    es.flatMap g = (List.range es.length).flatMap f := by
  induction es generalizing f with
  | nil => rfl
  | cons a es ih =>
    rw [List.flatMap_cons, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map, h 0 a rfl, ih (fun m => f (m + 1)) (fun m e he => h (m + 1) e (by simpa using he))]

theorem map_eq_range {α β : Type} (L : List α) (f : α → β) :
    L.map f = (List.range L.length).flatMap (fun m => (L[m]?).toList.map f) := by
  rw [← flatMap_eq_range L (fun a => [f a])]
  · induction L with
    | nil => rfl
    | cons a L ih => simp [ih]
  · intro m e he; rw [he]; rfl

variable [GooseExts] [GoGlobalContext]

/-- **`n`'s entries' global families** (see the module doc). -/
theorem tail_glob {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) :
    ∃ (Sb : Nat → List Nat) (Eb : Nat → List El),
      E = (List.range r'.ws.length).flatMap
        (fun m => if r'.nv.isLeaf' = true then (r'.ws[m]?).toList.map wEl else Eb m) ∧
      (∀ s ∈ D, s ∈ ownSl X'.v r'.nv.pgid' ++
          (List.range r'.ws.length).flatMap (fun m => pgSlots (spP X') (Sb m)) ∨
        s ∈ pendSlots w'.fl) ∧
      (∀ s ∈ ownSl X'.v r'.nv.pgid' ++
          (List.range r'.ws.length).flatMap (fun m => pgSlots (spP X') (Sb m)),
        s ∈ D ∨ newSlot st X.t.mv.pgid'.toNat s) ∧
      (∀ x, spP X' !! x ≠ spP X !! x → x ∉ D) ∧
      slotInv w'.fl X'.t.mv.pgid'.toNat (O ++ (ownSl X'.v r'.nv.pgid' ++
          (List.range r'.ws.length).flatMap (fun m => pgSlots (spP X') (Sb m)))) ∧
      ∀ m e, r'.ws[m]? = some e →
        (r'.nv.isLeaf' = true → (isBktFlag e.flags → bvalS (spP X') X'.t.mv.pgid'.toNat e.value (Sb m)) ∧
          (¬ isBktFlag e.flags → Sb m = [])) ∧
        (r'.nv.isLeaf' = false → fTree (spP X') X'.t.mv.pgid'.toNat e.pgid.toNat e.key
          (childHi hi (wKey r'.ws) r'.ws.length m) (h - 1) (Sb m) (Eb m)) := by
  obtain ⟨hn, -, hc⟩ := hpre
  rcases hc with ⟨hs, -⟩ | ⟨hut, -, hsl, -⟩
  · rw [hsp] at hs; cases hs
  rcases hend with ⟨hleaf, rfl, rfl, rfl, rfl, rfl⟩ | ⟨hleaf, h', es, i, rfl, hl, hcl, -⟩
  · cases hut with
    | branch _ r _ _ _ _ hr _ hlf =>
      rw [hn] at hr; cases hr; rw [hleaf] at hlf; cases hlf
    | leaf _ r _ _ Sb hr _ _ _ hbk hnb =>
      rw [hn] at hr; cases hr
      refine ⟨Sb, fun _ => [], ?_, fun s hs => Or.inl hs, fun s hs => Or.inl hs,
        fun x hx => absurd rfl hx, hsl, fun m e he => ⟨fun _ => ⟨hbk m e he, hnb m e he⟩,
          fun hf => by rw [hleaf] at hf; cases hf⟩⟩
      rw [map_eq_range]
      exact flatMap_congr_mem fun m _ => by rw [if_pos hleaf]
  · have hb := hl.br
    have hspl : ∀ c ∈ r'.cs, spilledN X' bl c := by
      intro c hc
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hc
      exact hl.done k c (Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hk).1 hcl) hk
    have hfam : ∀ m, ∃ (S : List Nat) (Ee : List El), ∀ e u, r'.ws[m]? = some e → es[m]? = some u →
        u = ⟨none, [], pgSlots (spP X') S, [], Ee⟩ ∧
        fTree (spP X') X'.t.mv.pgid'.toNat e.pgid.toNat e.key
          (childHi hi (wKey r'.ws) r'.ws.length m) h' S Ee := by
      intro m
      cases hw : r'.ws[m]? with
      | none => exact ⟨[], [], fun e u he => by cases he⟩
      | some e =>
        cases hu : es[m]? with
        | none => exact ⟨[], [], fun e u _ hu' => by cases hu'⟩
        | some u =>
          obtain ⟨S, Ee, hS, hf⟩ := uEnt_fin_of_spilled (hb.ent m e u hw hu) hspl
          refine ⟨S, Ee, fun e' u' he' hu' => ?_⟩
          cases he'; cases hu'
          exact ⟨hS, hf⟩
    let Sb : Nat → List Nat := fun m => Classical.choose (hfam m)
    let Eb : Nat → List El := fun m => Classical.choose (Classical.choose_spec (hfam m))
    have hSE : ∀ m e u, r'.ws[m]? = some e → es[m]? = some u →
        u = ⟨none, [], pgSlots (spP X') (Sb m), [], Eb m⟩ ∧
        fTree (spP X') X'.t.mv.pgid'.toNat e.pgid.toNat e.key
          (childHi hi (wKey r'.ws) r'.ws.length m) h' (Sb m) (Eb m) :=
      fun m => Classical.choose_spec (Classical.choose_spec (hfam m))
    have hget : ∀ (m : Nat) (u : UE), es[m]? = some u → ∃ e, r'.ws[m]? = some e := by
      intro m u hu
      have hlt : m < r'.ws.length := by rw [← hb.len]; exact (List.getElem?_eq_some_iff.1 hu).1
      exact ⟨_, List.getElem?_eq_getElem hlt⟩
    have hD : es.flatMap UE.D = (List.range r'.ws.length).flatMap (fun m => pgSlots (spP X') (Sb m)) := by
      rw [← hb.len]
      refine flatMap_eq_range es UE.D _ fun m u hu => ?_
      obtain ⟨e, he⟩ := hget m u hu
      rw [(hSE m e u he hu).1]
    have hE : es.flatMap UE.E = (List.range r'.ws.length).flatMap (fun m => Eb m) := by
      rw [← hb.len]
      refine flatMap_eq_range es UE.E _ fun m u hu => ?_
      obtain ⟨e, he⟩ := hget m u hu
      rw [(hSE m e u he hu).1]
    have hlf' : r'.nv.isLeaf' = false := hb.leaf
    refine ⟨Sb, Eb, ?_, ?_, ?_, hl.Pd, ?_, fun m e he => ⟨fun h1 => (by rw [hlf'] at h1; cases h1),
      fun _ => ?_⟩⟩
    · rw [← hl.EE, hE]
      exact flatMap_congr_mem fun m _ => by rw [if_neg (by rw [hlf']; exact Bool.false_ne_true)]
    · intro s hs; rw [← hD]; exact hl.Dk s hs
    · intro s hs; rw [← hD] at hs; exact hl.Dn s hs
    · rw [← hD]; exact hl.slot
    · have hlt : m < es.length := by rw [hb.len]; exact (List.getElem?_eq_some_iff.1 he).1
      exact (hSE m e _ he (List.getElem?_eq_getElem hlt)).2

end glob

end Spill

end bbolt
end EtcdGrove
end Perennial
