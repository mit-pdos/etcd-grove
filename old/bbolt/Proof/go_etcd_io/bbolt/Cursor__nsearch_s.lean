module
public import Spec.go_etcd_io.bbolt.Cursor__nsearch_s
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElements
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Key
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Cursor.nsearch.wp_sproof (hLPEs : Page.LeafPageElements.spec (GF := GF) (hG := hG))
    (hCount : Page.Count.spec (GF := GF) (hG := hG))
    (hKey : leafPageElement.Key.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG)) :
    Cursor.nsearch.sspec (GF := GF) (hG := hG) := by
  intro cl cv dqc es rv q pg nv dqn ins dqs ens key kb dk Hlast Hpage Hnodes
  wp_start as ⟨Hcl, Hs, Hres, Hk⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have Hne : es ≠ [] := by intro h; subst h; simp at Hlast
  have Hpos : 0 < es.length := List.length_pos_iff.2 Hne
  have Hli : es[es.length - 1]? = some rv := by
    rw [List.getLast?_eq_getElem?] at Hlast; exact Hlast
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  have Hix : (sint.Z (cv.stack'.len - W64 1)).toNat = es.length - 1 := by word
  icases ownSlice_elem_acc (sint.Z (cv.stack'.len - W64 1)) rv _ _ es (by word)
    (by rw [Hix]; exact Hli) $$ Hs with ⟨Hr, Hsback⟩
  try wp_auto
  by_cases Hnode : rv.node' = null
  · obtain ⟨Hc, Hlen, Hleaf, Hwf⟩ := Hpage Hnode
    unfold leafRes
    rw [if_pos Hnode]
    icases Hres with Hpg
    rw [Hnode]
    try wp_auto
    icases (page_header_bytes (hG := hG) _ q pg Hlen Hc).1 $$ Hpg with ⟨Hhd, Hrest⟩
    wp_apply hLPEs _ (pageOf pg) q Hc $$ [Hhd] as Hhd
    · iframe
    try wp_auto
    wp_apply hCount _ (pageOf pg) q $$ [Hhd] as Hhd
    · iframe
    try wp_auto
    have Hcnt : pageCount pg < 65536 := by have := leAt_lt pg 10 2; unfold pageCount; omega
    have Hu16 : uint.Z (W16 ((pageCount pg : Nat) : Int)) = ((pageCount pg : Nat) : Int) := by word
    have Hs64 : sint.Z (W64 ((pageCount pg : Nat) : Int)) = ((pageCount pg : Nat) : Int) := by word
    rw [Hu16]
    ihave Hpg := (page_header_bytes (hG := hG) _ q pg Hlen Hc).2 $$ [$Hhd $Hrest]
    obtain ⟨Hle, Helems, Hkvs, Hsorted⟩ := Hwf
    wp_apply sort.wp_Search (W64 ((pageCount pg : Nat) : Int)) _ (leafGE pg kb)
      iprop(inodes_ptr ↦ (if W16 ((pageCount pg : Nat) : Int) = W16 0 then slice.nil
        else slice.mk (rv.page' +ₗ 16) (W64 ((pageCount pg : Nat) : Int)) (W64 ((pageCount pg : Nat) : Int))) ∗
        key_ptr ↦ key ∗ key ↦*{dk} kb ∗ bytesPointsto rv.page' q pg) $$ [inodes key Hk Hpg]
    · rw [Hu16] at *
      iframe
      isplitl []
      · ipureintro; word
      isplitl []
      · unfold sort.predImplements
        iintro %i
        wp_start as ⟨⟨Hin, Hkp, Hk, Hpg⟩, %Hb⟩
        rw [Hs64] at Hb
        have Hcne : W16 ((pageCount pg : Nat) : Int) ≠ W16 0 := by
          intro h; have := congrArg BitVec.toNat h; simp at this; omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false Hcne)]
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hb.1, by word⟩)]
        have Hit : (sint.Z i).toNat < pageCount pg := by omega
        have Hidx : sliceIndexRef internal.common.leafPageElement (sint.Z i)
            (slice.mk (rv.page' +ₗ 16) (W64 ((pageCount pg : Nat) : Int)) (W64 ((pageCount pg : Nat) : Int))) =
            rv.page' +ₗ ((elemOff (sint.Z i).toNat : Nat) : Int) := by
          unfold sliceIndexRef arrayIndexRef
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa [Loc.add] using Hc)),
            typeSize_leafPageElement (hG := hG), loc_add_assoc]
          unfold elemOff; congr 1; omega
        rw [Hidx]
        try wp_auto
        have Hin' : elemOff (sint.Z i).toNat + 16 ≤ pg.length := by unfold elemOff at *; omega
        icases (leafElem_in_page (hG := hG) rv.page' q pg _ Hin' Hc).1 $$ Hpg with ⟨Hpre, He, Hpost⟩
        obtain ⟨Hk1, Hk2⟩ := Hkvs _ Hit
        have Hec : (rv.page' +ₗ ((elemOff (sint.Z i).toNat : Nat) : Int)).locCar ≠ 0 := by
          simpa [Loc.add] using Hc
        have HpL : leafPos pg (sint.Z i).toNat < 2 ^ 32 := leAt_lt _ _ 4
        have HkL : leafKsize pg (sint.Z i).toNat < 2 ^ 32 := leAt_lt _ _ 4
        have Hpu : uint.Z (W32 ((leafPos pg (sint.Z i).toNat : Nat) : Int)) =
            (leafPos pg (sint.Z i).toNat : Int) := by word
        have Hku : uint.Z (W32 ((leafKsize pg (sint.Z i).toNat : Nat) : Int)) =
            (leafKsize pg (sint.Z i).toNat : Int) := by word
        have HkOk : uint.Z (leafElemOf pg (sint.Z i).toNat).pos' +
            uint.Z (leafElemOf pg (sint.Z i).toNat).ksize' ≤ 2147483647 := by
          simp only [leafElemOf]; rw [Hpu, Hku]; omega
        wp_apply hKey _ (leafElemOf pg _) q Hec HkOk $$ [He] as He
        · iframe
        ihave Hpg := (leafElem_in_page (hG := hG) rv.page' q pg _ Hin' Hc).2 $$ [$Hpre $He $Hpost]
        simp only [Hpu, Hku, loc_add_assoc]
        have Hks : elemOff (sint.Z i).toNat + leafPos pg (sint.Z i).toNat +
            leafKsize pg (sint.Z i).toNat ≤ pg.length := by omega
        icases bytes_slice_acc (hG := hG) rv.page' q pg _ _ Hks HkL Hc $$ Hpg with ⟨Hks, Hpgback⟩
        unfold sliceAt
        rw [show (((elemOff (sint.Z i).toNat + leafPos pg (sint.Z i).toNat : Nat) : Int)) =
          ((elemOff (sint.Z i).toNat : Nat) : Int) + (leafPos pg (sint.Z i).toNat : Int) by omega]
        try wp_auto
        wp_apply bytes.wp_Compare _ key q dk _ kb $$ [Hks Hk] as ⟨Hks, Hk⟩
        · iframe
        try wp_auto
        ispecialize Hpgback $$ Hks
        iapply HΦ
        iframe
        ipureintro
        simp only [leafGE, leafKey, ne_eq, ← decide_not]
        exact decide_eq_decide.mpr Iff.rfl
      ipureintro; rw [Hs64]; exact leafGE_mono pg kb Hsorted
    iintro %idx ⟨⟨Hin, Hkp, Hk, Hpg⟩, %H0, %Hfound, %Hoob, %Hgt⟩
    rw [Hs64] at Hfound Hoob
    have Hle' : sint.Z idx ≤ (pageCount pg : Int) := by
      refine Classical.byContradiction fun hcn => ?_
      have := Hoob (fun j hj => Hgt j ⟨hj.1, by omega⟩)
      omega
    try wp_auto
    ispecialize Hsback $$ %({ rv with index' := idx } : elemRef) Hr
    rw [Hix]
    ispecialize HΦ $$ %idx
    try rw [Hnode]
    iapply HΦ
    iframe
    ipureintro
    refine ⟨H0, fun _ => Hle', fun h => absurd rfl h, fun _ => ?_⟩
    refine keysIdx_search (keysFn_range _ _) kb idx H0 Hle' (fun h => ?_) (fun k hk => ?_)
    · exact (geTrue_iff _ _).1 (Hfound h)
    · exact (geFalse_iff _ _).1 (Hgt k hk)

  · have Hsorted := Hnodes Hnode
    unfold leafRes
    rw [if_neg Hnode]
    icases Hres with ⟨Hn, Hins, Ho⟩
    ihave %Hisl := ownSlice_len _ _ _ $$ Hins
    ihave %Hol := inodesOwn_length _ _ $$ Ho
    rw [decide_eq_false Hnode, Bool.not_false]
    try wp_auto
    have Hlen : sint.Z nv.inodes'.len = (ens.length : Int) := by word
    wp_apply sort.wp_Search nv.inodes'.len _ (entryGE ens kb)
      iprop(n_ptr ↦ rv.node' ∗ key_ptr ↦ key ∗ rv.node' ↦{dqn} nv ∗ nv.inodes' ↦*{dqs} ins ∗
        inodesOwn ins ens ∗ key ↦*{dk} kb) $$ [n key Hn Hins Ho Hk]
    · iframe
      isplitl []
      · ipureintro; word
      isplitl []
      · unfold sort.predImplements
        iintro %i
        wp_start as ⟨⟨Hnp, Hkp, Hn, Hins, Ho, Hk⟩, %Hb⟩
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hb.1, by word⟩)]
        list_elem ins (sint.Z i).toNat as it
        list_elem ens (sint.Z i).toNat as e
        icases ownSlice_elem_acc (sint.Z i) it _ _ ins Hb.1 Hit_lookup $$ Hins with ⟨Hit, Hsback⟩
        wp_apply hK $$ [$Hit] as Hit
        try wp_auto
        icases inodesOwn_key_acc _ _ _ it e Hit_lookup He_lookup $$ Ho with ⟨Hkk, Hoback⟩
        wp_apply bytes.wp_Compare _ _ _ _ _ _ $$ [Hkk Hk] as ⟨Hkk, Hk⟩
        · iframe
        try wp_auto
        ispecialize Hoback $$ Hkk
        ihave Hins := Hsback $$ Hit
        rw [list_set_lookup_self _ _ _ Hit_lookup]
        iapply HΦ
        iframe
        ipureintro
        have Hek : entryKey ens (sint.Z i).toNat = e.key := by
          unfold entryKey; rw [He_lookup]; rfl
        simp only [entryGE, Hek, ne_eq, ← decide_not]
      ipureintro; rw [Hlen]; exact entryGE_mono ens kb Hsorted
    iintro %idx ⟨⟨Hnp, Hkp, Hn, Hins, Ho, Hk⟩, %H0, %Hfound, %Hoob, %Hgt⟩
    rw [Hlen] at Hfound Hoob
    have Hsi := isSearchIdx_of_search ens kb idx H0 Hfound Hoob Hgt
    try wp_auto
    ispecialize Hsback $$ %({ rv with index' := idx } : elemRef) Hr
    rw [Hix]
    ispecialize HΦ $$ %idx
    iapply HΦ
    iframe
    ipureintro
    exact ⟨H0, fun h => absurd h Hnode, fun _ => Hsi, fun h => absurd h Hnode⟩

end proof

end bbolt
end EtcdGrove
end Perennial
