/-
(hraft_robust R3) A fully owned slice of `raft.Log` values has fewer than `maxAddr` elements (each element's
`Index` field is a heap cell of its own: Perennial's `ownSlice_length_lt_maxAddr_of_cells`, through that
field). What `insert`'s `make([]raft.Log, 0, len(d.ents)+1)` needs.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Defs

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open Iris Iris.BI Iris.ProofMode BigSepL github_com.hashicorp.raft

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- A `Log` cell holds its `Index` field's heap cell. -/
theorem log_index_cell (l : Loc) (lv : Log) :
    typedPointstoDef (GF := GF) l lv (DFrac.own 1) ⊢
      heapPointsto (structFieldRef Log go!"Index" l) (DFrac.own 1) (LitV (LitByte (BitVec.ofNat 8 lv.Index'.toNat))) := by
  simp only [TypedPointsto.typedPointstoDef]
  refine BI.Entails.trans sep_elim_left ?_
  refine BI.Entails.trans (typedPointsto_split (structFieldRef Log go!"Index" l) lv.Index' (DFrac.own 1)) ?_
  simp only [TypedPointsto.typedPointstoDef]
  rw [show natBytes 8 lv.Index'.toNat = BitVec.ofNat 8 lv.Index'.toNat :: natBytes 7 (lv.Index'.toNat / 256) from rfl]
  simp only [bytesPointsto]
  exact sep_elim_left

theorem log_cells_mono (s : GoSlice) (vs : List Log) :
    ([∗list] i ↦ ve ∈ vs, typedPointsto (GF := GF) (arrayIndexRef Log (i : Int) s.ptr) ve (DFrac.own 1)) ⊢
      [∗list] i ↦ ve ∈ vs, heapPointsto (structFieldRef Log go!"Index" (arrayIndexRef Log (i : Int) s.ptr))
        (DFrac.own 1) (LitV (LitByte (BitVec.ofNat 8 ve.Index'.toNat))) :=
  bigSepL_mono_of_forall (fun {_ x} => BI.Entails.trans (typedPointsto_split _ _ _) (log_index_cell _ x))

/-- **A fully owned `Log` slice has fewer than `maxAddr` elements.** -/
theorem ownSlice_log_length_lt (s : GoSlice) (vs : List Log) :
    (s ↦* vs : IProp GF) ⊢ ⌜(vs.length : Int) < maxAddr⌝ := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  simp only [TypedPointsto.typedPointstoDef]
  iintro (%H | ⟨⟨⟨%_, He⟩, _⟩, %_⟩)
  · obtain ⟨_, rfl⟩ := H
    ipureintro; simp [maxAddr]
  · icases log_cells_mono s vs $$ He with He
    icases own_cells_addrs (fun i => structFieldRef Log go!"Index" (arrayIndexRef Log (i : Int) s.ptr)) vs
      (fun _ v => LitV (LitByte (BitVec.ofNat 8 v.Index'.toNat))) $$ He with %Hih
    obtain ⟨Hnd, Hb⟩ := Hih
    ipureintro
    have hm0 : (0 : Int) ≤ maxAddr := by simp [maxAddr]
    have em : ((maxAddr.toNat : Nat) : Int) = maxAddr := Int.toNat_of_nonneg hm0
    have hlt := nodup_length_lt_of_bounded
      ((List.range vs.length).map (fun (i : Nat) =>
        (structFieldRef Log go!"Index" (arrayIndexRef Log (i : Int) s.ptr)).addr.toNat))
      maxAddr.toNat (by simp [maxAddr]) Hnd (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        have := Hb i (List.mem_range.1 hi)
        have e : (((structFieldRef Log go!"Index" (arrayIndexRef Log (i : Int) s.ptr)).addr.toNat : Nat) : Int) =
            (structFieldRef Log go!"Index" (arrayIndexRef Log (i : Int) s.ptr)).addr := Int.toNat_of_nonneg (by omega)
        omega)
    simp only [List.length_map, List.length_range] at hlt
    omega

/-- A pair inserted in the middle of a `[∗list]` of two lists. -/
theorem bigSepL2_insert_mid {A B : Type} (Φ : A → B → IProp GF) (l1 : List A) (l2 : List B) (i : Nat)
    (x : A) (y : B) (hl : l1.length = l2.length) :
    ([∗list] a; b ∈ l1; l2, Φ a b) ∗ Φ x y ⊢
      [∗list] a; b ∈ l1.take i ++ x :: l1.drop i; l2.take i ++ y :: l2.drop i, Φ a b := by
  iintro ⟨H, Hxy⟩
  have hlt : (l1.take i).length = (l2.take i).length := by simp [List.length_take, hl]
  ihave H : ([∗list] a; b ∈ l1.take i ++ l1.drop i; l2.take i ++ l2.drop i, Φ a b) $$ [H]
  · rw [List.take_append_drop, List.take_append_drop]; iexact H
  ihave H := (BigSepL2.bigSepL2_append (Or.inl hlt)).1 $$ H
  icases H with ⟨H1, H2⟩
  iapply (BigSepL2.bigSepL2_append (Or.inl hlt)).2
  iframe H1
  iapply BigSepL2.bigSepL2_cons.2
  iframe

end lemmas

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
