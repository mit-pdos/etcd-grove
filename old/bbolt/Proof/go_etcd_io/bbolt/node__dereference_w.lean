module
public import Spec.go_etcd_io.bbolt.node__dereference_w
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetKey
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetValue
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.TxStats__IncNodeDeref

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

theorem node.dereference.wp_wproof (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hV : Inode.Value.spec (GF := GF) (hG := hG))
    (hSK : Inode.SetKey.spec (GF := GF) (hG := hG))
    (hSV : Inode.SetValue.spec (GF := GF) (hG := hG))
    (hA : Assert.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncNodeDeref.spec (GF := GF) (hG := hG)) :
    node.dereference.wspec (GF := GF) (hG := hG) := by
  intro g d
  induction d with
  | zero =>
    intro nl bl bv dqb st
    wp_start as ⟨Ht, _⟩
    icases (nodeTreeW_zero _ _ _).1 $$ Ht with %Hf
    exact Hf.elim
  | succ d ih =>
    intro nl bl bv dqb st
    wp_start as ⟨Ht, Hb, Hst⟩
    icases (nodeTreeW_succ _ _ _ _).1 $$ Ht with ⟨%nv, Hn, Hcs, Hpre, Hkids⟩
    unfold derefPreW
    icases Hpre with ⟨%Hpp, Hs, Ho, Hkey⟩
    obtain ⟨Hnv, Hbl, Hkeys⟩ := Hpp
    obtain ⟨cs, Hcsd⟩ : ∃ cs, cs = (g nl).cs := ⟨_, rfl⟩
    obtain ⟨ins, Hinsd⟩ : ∃ ins, ins = (g nl).ins := ⟨_, rfl⟩
    obtain ⟨es, Hesd⟩ : ∃ es, es = (g nl).es := ⟨_, rfl⟩
    obtain ⟨kb, Hkbd⟩ : ∃ kb, kb = (g nl).kb := ⟨_, rfl⟩
    obtain ⟨dk, Hdkd⟩ : ∃ dk, dk = (g nl).dk := ⟨_, rfl⟩
    rw [← Hcsd, ← Hinsd, ← Hesd, ← Hkbd, ← Hdkd]
    rw [← Hesd] at Hkeys
    ihave %Hsl := ownSlice_len _ _ _ $$ Hs
    ihave %Hol := inodesOwn_length _ _ $$ Ho
    ihave %Hcsl := ownSlice_len _ _ _ $$ Hcs
    wp_auto
    wp_join iprop(n_ptr ↦ nl ∗ ∃ (k1 : GoSlice), nl ↦ ({ nv with key' := k1 } : node) ∗
        (⌜nv.key' = slice.nil ∧ k1 = slice.nil⌝ ∨ (⌜nv.key' ≠ slice.nil⌝ ∗ nv.key' ↦*{dk} kb ∗ k1 ↦* kb)))
      at next with [n Hn Hkey] as ⟨n, %k1, Hn, Hk1⟩
    · by_cases hk : nv.key' = slice.nil
      · rw [decide_eq_true hk]
        try wp_auto
        iframe
        isplitl []
        · ipureintro; rfl
        ileft; ipureintro; exact ⟨hk, hk⟩
      · rw [decide_eq_false hk]
        try wp_auto
        icases Hkey with (%Hnil | ⟨Hkb, %Hkpos⟩)
        · exact absurd Hnil hk
        ihave %Hkbl := ownSlice_len _ _ _ $$ Hkb
        wp_apply wp_slice_make2 (V := w8) nv.key'.len $$ [] as %kn ⟨Hkn, -⟩
        · ipureintro; exact Hkbl.2
        try wp_auto
        wp_apply wp_slice_copy kn _ nv.key' kb dk $$ [Hkn Hkb] as %ncp ⟨_, Hkn, Hkb⟩
        · iframe
        have Hcp : kb.take (List.replicate (sint.nat nv.key'.len) (zero_val w8)).length ++
            (List.replicate (sint.nat nv.key'.len) (zero_val w8)).drop kb.length = kb := by
          rw [List.length_replicate, ← Hkbl.1, List.take_length, List.drop_replicate, Nat.sub_self,
            List.replicate_zero, List.append_nil]
        rw [Hcp]
        try wp_auto
        wp_if_destruct
        · wp_apply hA
          try wp_auto
          iframe
          isplitl []
          · ipureintro; rfl
          iright; iframe; ipureintro; exact hk
        · have Hk0 : 0 < kb.length := Hkpos.resolve_left Hif
          ihave %Hknl := ownSlice_len _ _ _ $$ Hkn
          rw [decide_eq_true (show sint.Z (W64 0) < sint.Z kn.len by word)]
          wp_apply hA
          try wp_auto
          iframe
          isplitl []
          · ipureintro; rfl
          iright; iframe; ipureintro; exact hk
    rename_i ip0
    irename : (i_ptr ↦ W64 0 : IProp GF) => Hi
    irename : (ip0 ↦ zero_val w64 : IProp GF) => Hci
    ihave IH : (∃ (j : w64) (pre : List internal.common.Inode),
        "i" ∷ i_ptr ↦ j ∗ "ci" ∷ (∃ v : w64, ip0 ↦ v) ∗
        "Hs" ∷ nv.inodes' ↦* (pre ++ ins.drop (sint.nat j)) ∗
        "Ho" ∷ inodesOwn (pre ++ ins.drop (sint.nat j))
          ((es.take (sint.nat j)).map freshEntry ++ es.drop (sint.nat j)) ∗
        "Hold" ∷ inodesOwn (ins.take (sint.nat j)) (es.take (sint.nat j)) ∗
        "Hn" ∷ nl ↦ ({ nv with key' := k1 } : node) ∗ "n" ∷ n_ptr ↦ nl ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nv.inodes'.len ∧ pre.length = sint.nat j⌝ :
        IProp GF) $$ [Hi Hci Hs Ho Hn n]
    · iexists W64 0, []
      simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero,
        List.map_nil, List.nil_append]
      iframe
      isplitl []
      · iapply inodesOwn_nil
      ipureintro; exact ⟨by decide, by word, rfl⟩
    wp_for IH
    icases ci with ⟨%cv0, ci⟩
    wp_if_destruct
    · have Hlt : sint.Z j < sint.Z nv.inodes'.len := by simpa using Hif
      clear Hif
      have Hjn : sint.nat j < ins.length := by word
      list_elem ins (sint.nat j) as it
      list_elem es (sint.nat j) as e
      have Hget := prefix_drop_get pre ins (sint.nat j) it Hj.2.2 Hit_lookup
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nv.inodes'.len
        from ⟨Hj.1, Hlt⟩))]
      wp_apply wp_load_slice_index _ (sint.Z j) _ _ it Hj.1 $$ [Hs] as Hs
      · iframe; ipureintro; exact Hget
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nv.inodes'.len
        from ⟨Hj.1, Hlt⟩))]
      icases ownSlice_elem_acc (sint.Z j) it _ _ _ Hj.1 Hget $$ Hs with ⟨Hit, Hsback⟩
      icases inodesOwn_step pre ins es (sint.nat j) it e Hj.2.2 Hit_lookup He_lookup $$ Ho
        with ⟨Hie, Hoback⟩
      unfold inodeIs
      icases Hie with ⟨%Hfp, Hik, Hiv⟩
      ihave %Hikl := ownSlice_len _ _ _ $$ Hik
      ihave %Hivl := ownSlice_len _ _ _ $$ Hiv
      have Hek : entryKey es (sint.nat j) = e.key := by unfold entryKey; rw [He_lookup]; rfl
      have Hkp : 0 < e.key.length := by rw [← Hek]; exact Hkeys _ (by omega)
      try wp_auto
      wp_apply hK $$ [$Hit] as Hit
      try wp_auto
      wp_apply wp_slice_make2 (V := w8) it.key'.len $$ [] as %kn ⟨Hkn, -⟩
      · ipureintro; exact Hikl.2
      try wp_auto
      wp_apply hK $$ [$Hit] as Hit
      try wp_auto
      wp_apply wp_slice_copy kn _ it.key' e.key e.kq $$ [Hkn Hik] as %ncp ⟨_, Hkn, Hik⟩
      · iframe
      rw [copy_fresh _ _ _ Hikl.1]
      try wp_auto
      wp_apply hSK $$ [$Hit] as Hit
      try wp_auto
      wp_apply hK $$ [$Hit] as Hit
      try wp_auto
      ihave %Hknl := ownSlice_len _ _ _ $$ Hkn
      rw [decide_eq_true (show sint.Z (W64 0) < sint.Z kn.len by word)]
      wp_apply hA
      try wp_auto
      wp_apply hV $$ [$Hit] as Hit
      try wp_auto
      wp_apply wp_slice_make2 (V := w8) it.value'.len $$ [] as %vn ⟨Hvn, -⟩
      · ipureintro; exact Hivl.2
      try wp_auto
      wp_apply hV $$ [$Hit] as Hit
      try wp_auto
      wp_apply wp_slice_copy vn _ it.value' e.value e.vq $$ [Hvn Hiv] as %ncp2 ⟨_, Hvn, Hiv⟩
      · iframe
      rw [copy_fresh _ _ _ Hivl.1]
      try wp_auto
      wp_apply hSV $$ [$Hit] as Hit
      try wp_auto
      try simp only
      ihave Hs := Hsback $$ Hit
      rw [show (sint.Z j).toNat = sint.nat j from rfl, prefix_drop_set _ _ _ _ _ Hj.2.2 Hit_lookup]
      ispecialize Hoback $$ %({ flags' := it.flags', pgid' := it.pgid', key' := kn, value' := vn } : internal.common.Inode)
      ihave Ho := Hoback $$ [Hkn Hvn]
      · simp only [freshEntry]; iframe; ipureintro; exact Hfp
      ihave Hold := inodesOwn_snoc_take ins es (sint.nat j) it e Hit_lookup He_lookup Hol $$ [Hold Hik Hiv]
      · iframe; unfold inodeIs; iframe; ipureintro; exact Hfp
      wp_for_post
      iframe
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      iexists j + W64 1, (pre ++ [({ flags' := it.flags', pgid' := it.pgid', key' := kn, value' := vn } : internal.common.Inode)])
      rw [Hj1]
      iframe
      isplitl [ci]
      · iexists _; iframe
      ipureintro
      exact ⟨by word, by word, by simp only [List.length_append, List.length_singleton]; omega⟩
    · have Hge : ¬ sint.Z j < sint.Z nv.inodes'.len := by simpa using Hif
      clear Hif
      have Hjn : sint.nat j = ins.length := by word
      have Hje : sint.nat j = es.length := by omega
      rw [Hjn, List.drop_length, List.append_nil, List.take_length]
      rw [show ins.length = es.length from Hol, List.take_length, List.drop_length, List.append_nil]
      try wp_auto
      irename : (i_ptr ↦ W64 0 : IProp GF) => Hi
      ihave IH2 : (∃ (j : w64) (k : w64),
          "i" ∷ i_ptr ↦ j ∗ "child" ∷ (∃ c : Loc, child_ptr ↦ c) ∗ "Hcs" ∷ nv.children' ↦* cs ∗
          "Hdone" ∷ ([∗list] c ∈ cs.take (sint.nat j), nodeTreeW (derefPostW g bl) g d c) ∗
          "Htodo" ∷ ([∗list] c ∈ cs.drop (sint.nat j), nodeTreeW (derefPreW g bl) g d c) ∗
          "Hb" ∷ bl ↦{dqb} bv ∗
          "Hst" ∷ structFieldRef Tx go!"stats" bv.tx' ↦ ({ st with NodeDeref' := st.NodeDeref' + k } : TxStats) ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nv.children'.len⌝ : IProp GF)
        $$ [Hi child Hcs Hkids Hb Hst]
      · iexists W64 0, W64 0
        simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
        iframe
        isplitl []
        · iapply BigSepL.bigSepL_nil.2; itrivial
        isplitl [Hst]
        · rw [show st.NodeDeref' + W64 0 = st.NodeDeref' by word]; iexact Hst
        ipureintro; exact ⟨by decide, by word⟩
      wp_for IH2
      icases child with ⟨%c0, child⟩
      wp_if_destruct
      · have Hlt : sint.Z j < sint.Z nv.children'.len := by simpa using Hif
        clear Hif
        have Hjn : sint.nat j < cs.length := by word
        list_elem cs (sint.nat j) as c
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nv.children'.len
          from ⟨Hj.1, Hlt⟩))]
        wp_apply wp_load_slice_index _ (sint.Z j) _ _ c Hj.1 $$ [Hcs] as Hcs
        · iframe; ipureintro; exact Hc_lookup
        try wp_auto
        rw [drop_cons_of_get _ _ _ Hc_lookup]
        icases (BigSepL.bigSepL_cons).1 $$ Htodo with ⟨Hc, Htodo⟩
        wp_apply ih c bl bv dqb _ $$ [Hc Hb Hst] as %k' ⟨Hc, Hb, Hst⟩
        · iframe
        try wp_auto
        ihave Hdone := (BigSepL.bigSepL_snoc (Φ := fun _ c => nodeTreeW (GF := GF) (derefPostW g bl) g d c) (l := cs.take (sint.nat j)) (x := c)).2 $$ [Hdone Hc]
        · iframe
        rw [← take_succ_of_get _ _ _ Hc_lookup]
        simp only
        rw [show st.NodeDeref' + k + k' = st.NodeDeref' + (k + k') by word]
        have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        wp_for_post
        iframe
        iexists j + W64 1, k + k'
        rw [Hj1]
        iframe
        isplitl [child]
        · iexists _; iframe
        ipureintro; exact ⟨by word, by word⟩
      · have Hge : ¬ sint.Z j < sint.Z nv.children'.len := by simpa using Hif
        clear Hif
        have Hjn : sint.nat j = cs.length := by word
        rw [Hjn, List.take_length]
        try wp_auto
        rw [Hbl]
        try wp_auto
        wp_apply hInc $$ [$Hst] as %st' ⟨%Hst', Hst⟩
        try wp_auto
        ispecialize HΦ $$ %(k + W64 1)
        iapply HΦ
        iframe
        isplitr [Hst]
        · iapply (nodeTreeW_succ _ _ _ _).2
          iexists ({ nv with key' := k1 } : node)
          unfold derefPostW
          rw [← Hcsd, ← Hinsd, ← Hesd, ← Hkbd, ← Hdkd, ← Hnv]
          simp only
          rw [Hbl]
          iframe
        subst Hst'
        simp only
        rw [show st.NodeDeref' + k + W64 1 = st.NodeDeref' + (k + W64 1) by word]
        iexact Hst

end proof

end bbolt
end EtcdGrove
end Perennial
