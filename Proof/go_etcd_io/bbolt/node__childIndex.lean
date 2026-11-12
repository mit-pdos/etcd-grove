/-
The proof of `Spec/go_etcd_io/bbolt/node__childIndex.lean`: U8 (`notes/bbolt-proof-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.node__childIndex
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Perennial.Spec.sort.Search
public import Perennial.Spec.bytes.Compare
public import Proof.go_etcd_io.bbolt.Rebalance.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The search predicate of `childIndex`: entry `i`'s key is not below `kb`. -/
def ciPred (ws : List WEntry) (kb : List w8) (i : Int) : Bool :=
  decide (¬ go.GoStringLt (wKey ws i.toNat) kb)

theorem ciPred_mono (ws : List WEntry) (kb : List w8) (hs : wsSorted ws) :
    sort.IsMonoPred (ciPred ws kb) (ws.length : Int) := by
  intro i j hij hi
  simp only [ciPred, decide_eq_true_eq] at hi ⊢
  intro hj
  apply hi
  have hlt := hs i.toNat j.toNat (by omega) (by omega)
  exact go.goStringLt_trans hlt hj

theorem wsIdx_of_bounds (ws : List WEntry) (kb : List w8) (idx : Nat) (hle : idx ≤ ws.length)
    (hbelow : ∀ k < idx, go.GoStringLt (wKey ws k) kb)
    (hat : idx < ws.length → ¬ go.GoStringLt (wKey ws idx) kb) : wsIdx ws kb = idx := by
  induction ws generalizing idx with
  | nil => simp at hle; subst hle; rfl
  | cons w ws ih =>
    cases idx with
    | zero =>
      have h0 := hat (by simp)
      simp only [wKey, List.getElem?_cons_zero, Option.map_some, Option.getD_some] at h0
      simp [wsIdx, List.takeWhile_cons, h0]
    | succ idx =>
      have h0 := hbelow 0 (by omega)
      simp only [wKey, List.getElem?_cons_zero, Option.map_some, Option.getD_some] at h0
      have := ih idx (by simp at hle; omega)
        (fun k hk => by have := hbelow (k + 1) (by omega); simpa [wKey] using this)
        (fun hk => by have := hat (by simp; omega); simpa [wKey] using this)
      simp only [wsIdx] at this ⊢
      rw [List.takeWhile_cons_of_pos (by simpa using h0), List.length_cons, this]

theorem node.childIndex.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hS : sort.Search.spec (GF := GF) (hG := hG)) (hC : bytes.Compare.spec (GF := GF) (hG := hG)) :
    node.childIndex.spec (GF := GF) (hG := hG) := by
  intro v n bl r dq qv child cv dqc ks kb Hsorted Hlive Hks Hbase
  wp_start as ⟨Ho, Hv, Hc, Hck⟩
  unfold objOwn
  icases Ho with ⟨Hn, Hs, Hcap, Hws, Hch, Hchcap, Hkey⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
  icases (viewCells_halves qv v).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases srcOwn_acc qv.half v cv.key' ks kb Hks Hbase $$ [Hck Hv1] with ⟨%dk, Hck, Hckb⟩
  · iframe
  icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcnn⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  ihave Hn : (n ↦{dq} r.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  have Hlen : sint.Z r.nv.inodes'.len = (r.ws.length : Int) := by word
  wp_apply hS r.nv.inodes'.len _ (ciPred r.ws kb)
    iprop(n_ptr ↦ n ∗ child_ptr ↦ child ∗ n ↦{dq} r.nv ∗ r.nv.inodes' ↦*{dq} r.ins ∗
      ([∗list] it;w ∈ r.ins;r.ws, wOwn v true it w) ∗ viewCells qv.half v ∗
      child ↦{dqc} cv ∗ cv.key' ↦*{dk} kb) $$ [n child Hn Hs Hws Hv2 Hc Hck]
  · iframe
    isplitl []
    · ipureintro; word
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨⟨Hnp, Hcp, Hn, Hs, Hws, Hv2, Hc, Hck⟩, %Hb⟩
      iStructNamed Hn
      wp_auto
      ihave Hn : (n ↦{dq} r.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hb.1, Hb.2⟩)]
      list_elem r.ins (sint.Z i).toNat as it
      list_elem r.ws (sint.Z i).toNat as w
      icases ownSlice_elem_acc (sint.Z i) it _ _ r.ins Hb.1 Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
      wp_apply hK $$ [$Hit] as Hit
      try wp_auto
      icases BigSepL2.bigSepL2_lookup_acc Hit_lookup Hw_lookup $$ Hws with ⟨Hw1, Hwsback⟩
      unfold wOwn
      simp only [↓reduceIte]
      icases Hw1 with ⟨%Hfp, Hik, Hiv⟩
      have Hwks : w.ks ≠ Src.stale := (Hlive w (List.mem_of_getElem? Hw_lookup)).1
      icases srcOwn_acc qv.half v it.key' w.ks w.key Hwks Hbase $$ [Hik Hv2] with ⟨%dik, Hik, Hikb⟩
      · iframe
      icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcnn'⟩
      iStructNamed Hc
      wp_auto
      ihave Hc : (child ↦{dqc} cv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hcnn'
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      wp_apply hC $$ [Hik Hck] as ⟨Hik, Hck⟩
      · iframe
      try wp_auto
      icases Hikb $$ Hik with ⟨Hik, Hv2⟩
      ihave Hws := Hwsback $$ [Hik Hiv]
      · iframe; ipureintro; exact Hfp
      ihave Hs := Hsback $$ Hit
      rw [list_set_lookup_self _ _ _ Hit_lookup]
      iapply HΦ
      iframe
      ipureintro
      have Hek : wKey r.ws (sint.Z i).toNat = w.key := by
        unfold wKey; rw [Hw_lookup]; rfl
      simp only [ciPred, Hek, bytes.compareResult]
      by_cases hlt : go.GoStringLt w.key kb
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        split <;> decide
    ipureintro; rw [Hlen]; exact ciPred_mono r.ws kb Hsorted
  iintro %idx ⟨⟨Hnp, Hcp, Hn, Hs, Hws, Hv2, Hc, Hck⟩, %H0, %Hfound, %Hoob, %Hgt⟩
  rw [Hlen] at Hfound Hoob
  have Hle : sint.Z idx ≤ (r.ws.length : Int) := by
    rcases Int.lt_or_le (r.ws.length : Int) (sint.Z idx) with hc | hc
    · have := Hoob (fun k hk => Hgt k ⟨hk.1, by omega⟩)
      omega
    · exact hc
  have Hidx : wsIdx r.ws kb = sint.nat idx := by
    apply wsIdx_of_bounds r.ws kb _ (by word)
    · intro k hk
      have := Hgt (k : Int) ⟨by omega, by word⟩
      simpa [ciPred] using this
    · intro hk
      have := Hfound (by word)
      simpa [ciPred, show ((sint.Z idx).toNat) = sint.nat idx from rfl] using this
  try wp_auto
  icases Hckb $$ Hck with ⟨Hck, Hv1⟩
  have Hw : W64 (wsIdx r.ws kb : Int) = idx := by rw [Hidx]; word
  rw [Hw]
  iapply HΦ
  iframe
  iapply (viewCells_halves qv v).2
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
