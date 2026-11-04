/-
The proof of `Spec/go_etcd_io/bbolt/node__del.lean` (U7, `notes/bbolt-proof-plan.md`; ported from
`old/bbolt/Proof/go_etcd_io/bbolt/node__del.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.node__del
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Perennial.Spec.sort.Search
public import Perennial.Spec.bytes.Compare
public import Perennial.Spec.bytes.Equal
public import Proof.go_etcd_io.bbolt.Rebalance.Base
public import Proof.go_etcd_io.bbolt.Rebalance.SliceWithin
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

theorem node.del.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hS : sort.Search.spec (GF := GF) (hG := hG)) (hC : bytes.Compare.spec (GF := GF) (hG := hG))
    (hE : bytes.Equal.spec (GF := GF) (hG := hG)) :
    node.del.spec (GF := GF) (hG := hG) := by
  intro v n bl r qv key kb ks Hcapo Hsorted Hlive Hks Hbase
  wp_start as ⟨Ho, Hv, Hkp⟩
  unfold objOwn
  simp only [Hcapo, ↓reduceIte]
  icases Ho with ⟨Hn, Hs, Hcap, Hws, Hch, Hchcap, Hkey⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  icases (viewCells_halves qv v).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases srcOwn_acc qv.half v key ks kb Hks Hbase $$ [Hkp Hv1] with ⟨%dk, Hkp, Hkb⟩
  · iframe
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  irename key => Hfkey
  wp_auto
  ihave Hn : (n ↦ r.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled Hfkey pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  have Hlen : sint.Z r.nv.inodes'.len = (r.ws.length : Int) := by word
  wp_apply hS r.nv.inodes'.len _ (Write.gePred r.ws kb)
    iprop(n_ptr ↦ n ∗ key_ptr ↦ key ∗ n ↦ r.nv ∗ r.nv.inodes' ↦* r.ins ∗
      ([∗list] it;w ∈ r.ins;r.ws, wOwn v true it w) ∗ viewCells qv.half v ∗
      key ↦*{dk} kb) $$ [n key Hn Hs Hws Hv2 Hkp]
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
      by_cases hlt : go.GoStringLt w.key kb
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        split <;> decide
    ipureintro; rw [Hlen]; exact Write.gePred_mono r.ws kb Hsorted
  iintro %idx ⟨⟨Hnp, Hkp, Hn, Hs, Hws, Hv2, Hk⟩, %H0, %Hfound, %Hoob, %Hgt⟩
  rw [Hlen] at Hfound Hoob
  have Hle : sint.Z idx ≤ (r.ws.length : Int) := by
    rcases Int.lt_or_le (r.ws.length : Int) (sint.Z idx) with hc | hc
    · have := Hoob (fun k hk => Hgt k ⟨hk.1, by omega⟩)
      omega
    · exact hc
  have Hidx : wsIdx r.ws kb = sint.nat idx := by
    apply Write.wsIdx_of_bounds r.ws kb _ (by word)
    · intro k hk
      have := Hgt (k : Int) ⟨by omega, by word⟩
      simpa [Write.gePred] using this
    · intro hk
      have := Hfound (by word)
      simpa [Write.gePred, show ((sint.Z idx).toNat) = sint.nat idx from rfl] using this
  try wp_auto
  wp_if_destruct
  · -- past the end: not found
    have Hnf : ¬ wsFound r.ws kb := fun h => by
      have := ((Write.wsFound_iff _ _).1 h).1; rw [Hidx] at this; word
    try wp_auto
    icases Hkb $$ Hk with ⟨-, Hv1⟩
    iapply HΦ
    isplitl [Hn Hs Hcap Hws Hch Hchcap Hkey]
    · ileft
      isplitr
      · ipureintro; exact Hnf
      try unfold objOwn
      try simp only [Hcapo, ↓reduceIte]
      iframe
    iapply (viewCells_halves qv v).2
    iframe
  have Hlt : sint.nat idx < r.ws.length := by word
  list_elem r.ins (sint.nat idx) as it
  list_elem r.ws (sint.nat idx) as w
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z r.nv.inodes'.len
    from ⟨H0, by word⟩))]
  icases ownSlice_elem_acc (sint.Z idx) it _ _ r.ins H0 Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
  wp_apply hK $$ [$Hit] as Hit
  try wp_auto
  icases BigSepL2.bigSepL2_lookup_acc Hit_lookup Hw_lookup $$ Hws with ⟨Hw1, Hwsback⟩
  icases (Write.wOwn_live v it w).1 $$ Hw1 with ⟨%Hfp, Hik, Hiv⟩
  have Hwks : w.ks ≠ Src.stale := (Hlive w (List.mem_of_getElem? Hw_lookup)).1
  icases srcOwn_acc qv.half v it.key' w.ks w.key Hwks Hbase $$ [Hik Hv2] with ⟨%dik, Hik, Hikb⟩
  · iframe
  wp_apply hE $$ [Hik Hk] as ⟨Hik, Hk⟩
  · iframe
  icases Hikb $$ Hik with ⟨Hik, Hv2⟩
  ihave Hws := Hwsback $$ [Hik Hiv]
  · iapply (Write.wOwn_live v it w).2; iframe; ipureintro; exact Hfp
  ihave Hs := Hsback $$ Hit
  rw [list_set_lookup_self _ _ _ Hit_lookup]
  have Hek : wKey r.ws (sint.nat idx) = w.key := by
    unfold wKey; rw [Hw_lookup]; rfl
  icases Hkb $$ Hk with ⟨-, Hv1⟩
  ihave Hv := (viewCells_halves qv v).2 $$ [Hv1 Hv2]
  · iframe
  try wp_auto
  wp_if_destruct
  · -- the key there: removed
    have Hf : wsFound r.ws w.key := by
      rw [Write.wsFound_iff, Hidx, Hek]; exact ⟨Hlt, rfl⟩
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z idx ∧
      sint.Z idx ≤ sint.Z r.nv.inodes'.cap from ⟨by decide, H0, by word⟩))]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (idx + W64 1) ∧
      sint.Z (idx + W64 1) ≤ sint.Z r.nv.inodes'.len ∧ sint.Z r.nv.inodes'.len ≤ sint.Z r.nv.inodes'.cap
      from ⟨by word, by word, Hcw.2⟩))]
    try wp_auto
    wp_apply wp_slice_append_delete (st := Inodes.ty) r.nv.inodes' r.ins idx ⟨H0, by word⟩ $$ [Hs Hcap]
      as ⟨Hs, Hcap⟩
    · iframe
    try wp_auto
    ihave Hws := Write.wOwns_delete v r.ins r.ws (sint.nat idx) Hwl (by omega) $$ Hws
    iapply HΦ
    isplitl [Hn Hs Hcap Hws Hch Hchcap Hkey]
    · iright
      isplitr
      · ipureintro; exact Hf
      iexists _
      simp only [NRec.withEntsU, Hcapo, wsDelAt, Hf, Hidx, ↓reduceIte, List.eraseIdx_eq_take_drop_succ]
      iframe
    iframe
  · -- a different key there: not found
    have Hnf : ¬ wsFound r.ws kb := fun h => by
      have := ((Write.wsFound_iff _ _).1 h).2; rw [Hidx, Hek] at this
      exact Hif this
    try wp_auto
    iapply HΦ
    isplitl [Hn Hs Hcap Hws Hch Hchcap Hkey]
    · ileft
      isplitr
      · ipureintro; exact Hnf
      try unfold objOwn
      try simp only [Hcapo, ↓reduceIte]
      iframe
    iframe

end proof

end bbolt
end EtcdGrove
end Perennial
