/-
The writer's `W` bytes with the synced freelist page's half (`wBytesX`, session S4) against whole
`wBytes`: splitting the page's slots out (`Open`, which creates the store's half) and joining
them back (`Close`, which gets the store's half from `store_close`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section wbx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

private theorem bigSepL_mono_mem_x {A : Type} {Φ Ψ : A → IProp GF} {S : List A}
    (h : ∀ s ∈ S, Φ s ⊢ Ψ s) : ([∗list] s ∈ S, Φ s) ⊢ [∗list] s ∈ S, Ψ s :=
  BigSepL.bigSepL_mono fun {_ x} hk => h x (List.mem_of_getElem? hk)

/-- `wBytes` of a list split by membership in `X`. -/
theorem wBytes_split_filter (p : BFile) (W X : List Nat) (wb : Nat → List w8) (size : Nat) :
    wBytes (GF := GF) p W wb size ⊣⊢
      wBytes p (W.filter (fun s => decide (s ∉ X))) wb size ∗
        wBytes p (W.filter (fun s => decide (s ∈ X))) wb size := by
  unfold wBytes
  have hperm : (W.filter (fun s => decide (s ∉ X)) ++ W.filter (fun s => decide (s ∈ X))).Perm W := by
    have h := List.filter_append_perm (fun s => decide (s ∉ X)) W
    have e : W.filter (fun s => !decide (s ∉ X)) = W.filter (fun s => decide (s ∈ X)) := by
      apply List.filter_congr; intro s _; simp
    rw [e] at h; exact h
  exact (BigSepL.bigSepL_perm hperm).symm.trans BigSepL.bigSepL_append

/-- `wBytes` of slots inside the file are their `osSlot`s. -/
theorem wBytes_inside (p : BFile) (X : List Nat) (wb : Nat → List w8) (size : Nat)
    (h : ∀ s ∈ X, 4096 * (s + 1) ≤ size) :
    wBytes (GF := GF) p X wb size ⊣⊢ [∗list] s ∈ X, osSlot p s (wb s) := by
  unfold wBytes osSlot
  constructor
  · refine bigSepL_mono_mem_x fun s hs => ?_
    simp only [h s hs, ↓reduceIte]; exact .rfl
  · refine bigSepL_mono_mem_x fun s hs => ?_
    simp only [h s hs, ↓reduceIte]; exact .rfl

/-- The members of `W` in `X`, for `X ⊆ W` without repeats, are `X` up to order. -/
theorem filter_mem_perm (W X : List Nat) (hW : W.Nodup) (hX : X.Nodup) (hsub : ∀ s ∈ X, s ∈ W) :
    (W.filter (fun s => decide (s ∈ X))).Perm X := by
  rw [List.perm_ext_iff_of_nodup (hW.filter _) hX]
  intro s
  rw [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hsub s h, h⟩⟩

/-- **The synced freelist page's slots out of the writer's bytes**: their halves, the writer
keeping the other halves (`wBytesX`). -/
theorem wBytes_splitX (p : BFile) (W X : List Nat) (wb : Nat → List w8) (size : Nat)
    (hW : W.Nodup) (hX : X.Nodup) (hsub : ∀ s ∈ X, s ∈ W ∧ 4096 * (s + 1) ≤ size) :
    wBytes (GF := GF) p W wb size ⊢
      wBytesX p W X wb size ∗ [∗list] s ∈ X, osSlotH p s (wb s) := by
  refine (wBytes_split_filter p W X wb size).1.trans ?_
  unfold wBytesX
  refine (sep_mono .rfl ?_).trans sep_assoc.2
  have hin : ∀ s ∈ W.filter (fun s => decide (s ∈ X)), 4096 * (s + 1) ≤ size := by
    intro s hs
    rw [List.mem_filter, decide_eq_true_eq] at hs
    exact (hsub s hs.2).2
  refine (wBytes_inside p _ wb size hin).1.trans ?_
  refine (BigSepL.bigSepL_perm (filter_mem_perm W X hW hX fun s h => (hsub s h).1)).1.trans ?_
  exact osSlots_halves p wb X

/-- **The synced freelist page's slots back into the writer's bytes** (`Close`): the store's
halves `bs` agree with the writer's; the slots as a list `W` but `X`, then `X`. -/
theorem wBytes_joinX (p : BFile) (W X : List Nat) (wb bs : Nat → List w8) (size : Nat)
    (hsub : ∀ s ∈ X, 4096 * (s + 1) ≤ size)
    (hlen : ∀ s ∈ X, (wb s).length = (bs s).length) :
    wBytesX (GF := GF) p W X wb size ∗ ([∗list] s ∈ X, osSlotH p s (bs s)) ⊢
      wBytes p (W.filter (fun s => decide (s ∉ X)) ++ X) wb size ∗ ⌜∀ s ∈ X, bs s = wb s⌝ := by
  unfold wBytesX
  iintro ⟨⟨Hw, Hx⟩, Hs⟩
  icases osSlotsH_join p wb bs X hlen $$ [Hx Hs] with ⟨Hx, %h⟩
  · iframe
  have happ : wBytes (GF := GF) p (W.filter (fun s => decide (s ∉ X)) ++ X) wb size ⊣⊢
      wBytes p (W.filter (fun s => decide (s ∉ X))) wb size ∗ wBytes p X wb size := by
    unfold wBytes; exact BigSepL.bigSepL_append
  isplitl [Hw Hx]
  · iapply happ.2
    iframe Hw
    iapply (wBytes_inside p X wb size hsub).2
    iexact Hx
  · ipureintro; exact h

/-- Every member of `W` is one of `W` but `X`, then `X`. -/
theorem mem_filter_append (W X : List Nat) (s : Nat) (h : s ∈ W) :
    s ∈ W.filter (fun s => decide (s ∉ X)) ++ X := by
  by_cases hx : s ∈ X
  · exact List.mem_append_right _ hx
  · exact List.mem_append_left _ (List.mem_filter.2 ⟨h, by simpa using hx⟩)

end wbx

end bbolt
end EtcdGrove
end Perennial
