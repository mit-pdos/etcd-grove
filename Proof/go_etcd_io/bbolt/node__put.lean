/-
The proof of `Spec/go_etcd_io/bbolt/node__put.lean` (U7, `notes/bbolt-proof-plan.md`; ported from
`old/bbolt/Proof/go_etcd_io/bbolt/node__put.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.node__put
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetKey
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetValue
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetPgid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Perennial.Spec.sort.Search
public import Perennial.Spec.bytes.Compare
public import Perennial.Spec.bytes.Equal
public import Proof.go_etcd_io.bbolt.Rebalance.Base
public import Proof.go_etcd_io.bbolt.Write.NodeEnts

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

theorem node.put.wp_proof (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hSF : internal.common.Inode.SetFlags.spec (GF := GF) (hG := hG))
    (hSK : internal.common.Inode.SetKey.spec (GF := GF) (hG := hG))
    (hSV : internal.common.Inode.SetValue.spec (GF := GF) (hG := hG))
    (hSP : internal.common.Inode.SetPgid.spec (GF := GF) (hG := hG))
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hS : sort.Search.spec (GF := GF) (hG := hG)) (hC : bytes.Compare.spec (GF := GF) (hG := hG))
    (hE : bytes.Equal.spec (GF := GF) (hG := hG)) :
    node.put.spec (GF := GF) (hG := hG) := by
  intro v n bl r tx mp mv dqb qv oldKey newKey value okb nkb vb oks nks vs pgId flags
    Hbk Hcapo Hsorted Hlive Hpg Hok0 Hnk0 Hoks Hnks Hvs Hbase
  wp_start as ⟨Ho, Hv, Hbt, Htm, Hm, Hokp, #Hnkp, #Hvp⟩
  unfold objOwn
  simp only [Hcapo, ↓reduceIte]
  icases Ho with ⟨Hn, Hs, Hcap, Hws, Hch, Hchcap, Hkey⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
  icases (viewCells_halves qv v).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases srcOwn_acc qv.half v oldKey oks okb Hoks Hbase $$ [Hokp Hv1] with ⟨%dk, Hokp, Hokb⟩
  · iframe
  ihave %Hokl := ownSlice_len _ _ _ $$ Hokp
  icases srcOwn_acc qv.half v newKey nks nkb Hnks Hbase $$ [Hnkp Hv2] with ⟨%dnk, Hnks', Hnkb⟩
  · iframe; iexact Hnkp
  ihave %Hnkl := ownSlice_len _ _ _ $$ Hnks'
  icases Hnkb $$ Hnks' with ⟨-, Hv2⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  rw [Hbk]
  wp_auto
  wp_apply hPgid $$ [$Hm] as Hm
  try wp_auto
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · exfalso; word
  ihave Hn : (n ↦ r.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    rw [Hbk]
    iframe
  have Hlen : sint.Z r.nv.inodes'.len = (r.ws.length : Int) := by word
  wp_apply hS r.nv.inodes'.len _ (Write.gePred r.ws okb)
    iprop(n_ptr ↦ n ∗ oldKey_ptr ↦ oldKey ∗ n ↦ r.nv ∗ r.nv.inodes' ↦* r.ins ∗
      ([∗list] it;w ∈ r.ins;r.ws, wOwn v true it w) ∗ viewCells qv.half v ∗
      oldKey ↦*{dk} okb) $$ [n oldKey Hn Hs Hws Hv2 Hokp]
  · iframe
    isplitl []
    · ipureintro; word
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨⟨Hnp, Hkp, Hn, Hs, Hws, Hv2, Hk⟩, %Hb⟩
      iStructNamed Hn
      wp_auto
      ihave Hn : (n ↦ r.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
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
      wp_apply hC $$ [Hik Hk] as ⟨Hik, Hk⟩
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
      simp only [Write.gePred, Hek, bytes.compareResult]
      by_cases hlt : go.GoStringLt w.key okb
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        split <;> decide
    ipureintro; rw [Hlen]; exact Write.gePred_mono r.ws okb Hsorted
  iintro %idx ⟨⟨Hnp, Hkp, Hn, Hs, Hws, Hv2, Hokp⟩, %H0, %Hfound, %Hoob, %Hgt⟩
  rw [Hlen] at Hfound Hoob
  have Hle : sint.Z idx ≤ (r.ws.length : Int) := by
    rcases Int.lt_or_le (r.ws.length : Int) (sint.Z idx) with hc | hc
    · have := Hoob (fun k hk => Hgt k ⟨hk.1, by omega⟩)
      omega
    · exact hc
  have Hidx : wsIdx r.ws okb = sint.nat idx := by
    apply Write.wsIdx_of_bounds r.ws okb _ (by word)
    · intro k hk
      have := Hgt (k : Int) ⟨by omega, by word⟩
      simpa [Write.gePred] using this
    · intro hk
      have := Hfound (by word)
      simpa [Write.gePred, show ((sint.Z idx).toNat) = sint.nat idx from rfl] using this
  try wp_auto
  wp_join (Q := fun x => iprop(⌜x = #(decide (wsFound r.ws okb))⌝ ∗
      n_ptr ↦ n ∗ oldKey_ptr ↦ oldKey ∗ index_ptr ↦ idx ∗ n ↦ r.nv ∗ r.nv.inodes' ↦* r.ins ∗
      ([∗list] it;w ∈ r.ins;r.ws, wOwn v true it w) ∗ viewCells qv.half v ∗
      oldKey ↦*{dk} okb))
    at (if: _ then _ else _) with [Hnp Hkp index Hn Hs Hws Hv2 Hokp]
    as ⟨%Hx, Hnp, Hkp, index, Hn, Hs, Hws, Hv2, Hokp⟩
  · wp_if_destruct
    · wp_if_destruct
      · have Hlt : sint.nat idx < r.ws.length := by word
        list_elem r.ins (sint.nat idx) as it
        list_elem r.ws (sint.nat idx) as w
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z r.nv.inodes'.len
          from ⟨H0, by word⟩))]
        icases ownSlice_elem_acc (sint.Z idx) it _ _ r.ins H0 Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
        wp_apply hK $$ [$Hit] as Hit
        try wp_auto
        icases BigSepL2.bigSepL2_lookup_acc Hit_lookup Hw_lookup $$ Hws with ⟨Hw1, Hwsback⟩
        unfold wOwn
        simp only [↓reduceIte]
        icases Hw1 with ⟨%Hfp, Hik, Hiv⟩
        have Hwks : w.ks ≠ Src.stale := (Hlive w (List.mem_of_getElem? Hw_lookup)).1
        icases srcOwn_acc qv.half v it.key' w.ks w.key Hwks Hbase $$ [Hik Hv2] with ⟨%dik, Hik, Hikb⟩
        · iframe
        wp_apply hE $$ [Hik Hokp] as ⟨Hik, Hokp⟩
        · iframe
        icases Hikb $$ Hik with ⟨Hik, Hv2⟩
        ihave Hws := Hwsback $$ [Hik Hiv]
        · iframe; ipureintro; exact Hfp
        ihave Hs := Hsback $$ Hit
        rw [list_set_lookup_self _ _ _ Hit_lookup]
        have Hek : wKey r.ws (sint.nat idx) = w.key := by
          unfold wKey; rw [Hw_lookup]; rfl
        iframe
        ipureintro
        congr 1
        exact decide_eq_decide.mpr (by rw [Write.wsFound_iff, Hidx, Hek]; exact ⟨fun h => ⟨Hlt, h⟩, fun h => h.2⟩)
      · iframe
        ipureintro
        congr 1
        exact (decide_eq_false (fun h => by have := ((Write.wsFound_iff _ _).1 h).1; rw [Hidx] at this; word)).symm
    · iframe
      ipureintro
      congr 1
      exact (decide_eq_false (fun h => by have := ((Write.wsFound_iff _ _).1 h).1; rw [Hidx] at this; word)).symm
  subst Hx
  have Hile : sint.nat idx ≤ r.ins.length := by rw [Hwl]; word
  have Hpi := (decide_eq_true_iff (p := wsFound r.ws okb))
  generalize Hex : decide (wsFound r.ws okb) = ex at Hpi ⊢
  wp_auto
  wp_join iprop(∃ (s' : GoSlice) (L : List Inode),
      n_ptr ↦ n ∗ index_ptr ↦ idx ∗ n ↦ ({ r.nv with inodes' := s' } : node) ∗ s' ↦* L ∗
      ownSliceCap Inode s' (DFrac.own 1) ∗
      ⌜sint.nat idx < L.length ∧ ∀ x, L.set (sint.nat idx) x =
        if ex then r.ins.set (sint.nat idx) x
        else r.ins.take (sint.nat idx) ++ x :: r.ins.drop (sint.nat idx)⌝)
    at next with [Hn Hs Hcap Hnp index] as ⟨%s', %L, Hnp, index, Hn, Hs, Hcap, %HL⟩
  · cases ex
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1 ⟨Hs, Hcap, -⟩
      try wp_auto
      ihave %Hsl1 := ownSlice_len _ _ _ $$ Hs
      ihave %Hcw1 := ownSliceCap_wf _ _ $$ Hcap
      simp only [List.length_append, List.length_singleton] at Hsl1
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (idx + W64 1) ∧
        sint.Z (idx + W64 1) ≤ sint.Z s1.len ∧ sint.Z s1.len ≤ sint.Z s1.cap from
        ⟨by word, by word, Hcw1.2⟩))]
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z idx ∧
        sint.Z idx ≤ sint.Z s1.len ∧ sint.Z s1.len ≤ sint.Z s1.cap from
        ⟨H0, by word, Hcw1.2⟩))]
      try wp_auto
      wp_apply wp_slice_copy_within s1 _ (idx + W64 1) s1.len idx s1.len
        ⟨by word, by word, by word⟩ ⟨H0, by word, by word⟩ $$ [Hs] as %k ⟨_, Hs⟩
      · iframe
      try wp_auto
      rw [show sint.nat (idx + W64 1) = sint.nat idx + 1 by word,
        show sint.nat s1.len = r.ins.length + 1 by omega]
      isplitl []
      · ipureintro; rfl
      iexists s1, _
      iframe
      ipureintro
      have Hset := fun x => Write.insert_copy_list r.ins (zero_val Inode) x (sint.nat idx) Hile
      refine ⟨?_, fun x => by rw [Hset x]; rfl⟩
      have := congrArg List.length (Hset (zero_val Inode))
      rw [List.length_set] at this
      rw [this]
      simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
      omega
    · try wp_auto
      isplitl []
      · ipureintro; rfl
      iexists r.nv.inodes', r.ins
      iframe
      ipureintro
      have := ((Write.wsFound_iff _ _).1 (Hpi.1 rfl)).1
      exact ⟨by rw [Hidx] at this; omega, fun x => rfl⟩
  ihave %HsL := ownSlice_len _ _ _ $$ Hs
  list_elem L (sint.nat idx) as y
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z s'.len from
    ⟨H0, by word⟩))]
  icases ownSlice_elem_acc (sint.Z idx) y _ _ L H0 Hy_lookup $$ Hs with ⟨Hit, Hsback⟩
  try wp_auto
  wp_apply hSF $$ [$Hit] as Hit
  try wp_auto
  wp_apply hSK $$ [$Hit] as Hit
  try wp_auto
  wp_apply hSV $$ [$Hit] as Hit
  try wp_auto
  wp_apply hSP $$ [$Hit] as Hit
  try wp_auto
  wp_apply hK $$ [$Hit] as Hit
  try wp_auto
  rw [decide_eq_true (show sint.Z (W64 0) < sint.Z newKey.len by word)]
  wp_apply hA
  try wp_auto
  try simp only
  ihave Hs := Hsback $$ Hit
  rw [show (sint.Z idx).toNat = sint.nat idx from rfl, HL.2]
  icases Hokb $$ Hokp with ⟨-, Hv1⟩
  ihave Hv := (viewCells_halves qv v).2 $$ [Hv1 Hv2]
  · iframe
  iapply HΦ
  cases ex
  · have Hnf : ¬ wsFound r.ws okb := fun h => by have := Hpi.2 h; simp at this
    iexists s', (r.ins.take (sint.nat idx) ++
      (⟨flags, pgId, newKey, value⟩ : Inode) :: r.ins.drop (sint.nat idx))
    simp only [NRec.withEnts, Hcapo, Write.wsPutAt_eq, Hidx, Hnf, Bool.false_eq_true, ↓reduceIte]
    iframe
    iapply Write.wOwns_insert v r.ins r.ws (sint.nat idx) _ _ Hwl Hile
    iframe
    unfold wOwn
    simp only [↓reduceIte]
    isplitr
    · ipureintro; simp
    isplitl
    · iexact Hnkp
    · iexact Hvp
  · have Hf : wsFound r.ws okb := Hpi.1 rfl
    have Hlt := ((Write.wsFound_iff _ _).1 Hf).1
    rw [Hidx] at Hlt
    iexists s', (r.ins.set (sint.nat idx) (⟨flags, pgId, newKey, value⟩ : Inode))
    simp only [NRec.withEnts, Hcapo, Write.wsPutAt_eq, Hidx, Hf, ↓reduceIte]
    iframe
    iapply Write.wOwns_set v r.ins r.ws (sint.nat idx) _ _ Hwl (by omega)
    iframe
    unfold wOwn
    simp only [↓reduceIte]
    isplitr
    · ipureintro; simp
    isplitl
    · iexact Hnkp
    · iexact Hvp

end proof

end bbolt
end EtcdGrove
end Perennial
