/-
`node.dereference` (U9b, `notes/bbolt-proof-plan.md`; unit-internal, stated and proved here):
`n.dereference()` on a live node `n` of the bucket `bl` copies its key and every inode's key and
value to fresh heap slices (`nodeDerefd`), then dereferences its children: afterwards the nodes
below `n` hold no view slice (`covered`), and nothing but node records changed (`derefStep`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.DerefHeap
public import Proof.go_etcd_io.bbolt.Spill.DerefCopy
public import Proof.go_etcd_io.bbolt.Rebalance.Objs
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetKey
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetValue
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.TxStats__IncNodeDeref

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`n.dereference()`** of a live node `n` of the bucket `bl`. -/
abbrev node.dereference.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl n : Loc) (B : BRec),
  X.t.bs !! bl = some B → (B.ns !! n).isSome → n ∈ X.live → derefPre X → liveFresh X →
  {{ wtxW (GF := GF) K tx r m X }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"dereference")) (Val #()))
  {{ RET #(); ∃ X', wtxW K tx r m X' ∗ ⌜derefStep X X' ∧ covered X' bl n⌝ }}

end spec

theorem sint_nat_eq {n : Nat} (w : BitVec n) : sint.nat w = (sint.Z w).toNat := rfl

section wown
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem wOwn_true (v : View) (it : Inode) (w : WEntry) :
    wOwn (GF := GF) v true it w ⊣⊢ ⌜it.flags' = w.flags ∧ it.pgid' = w.pgid⌝ ∗
      srcOwn v it.key' w.ks w.key ∗ srcOwn v it.value' w.vs w.value := by
  unfold wOwn; simp only [↓reduceIte]; exact .rfl

end wown

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.dereference.wp_aux (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.Inode.Value.spec (GF := GF) (hG := hG))
    (hSK : internal.common.Inode.SetKey.spec (GF := GF) (hG := hG))
    (hSV : internal.common.Inode.SetValue.spec (GF := GF) (hG := hG))
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncNodeDeref.spec (GF := GF) (hG := hG)) :
    ⊢ (∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl n : Loc) (B : BRec),
      ⌜X.t.bs !! bl = some B ∧ (B.ns !! n).isSome ∧ n ∈ X.live ∧ derefPre X ∧ liveFresh X⌝ →
      ∀ Φ, wtxW K tx r m X -∗
        ▷ (∀ X', wtxW K tx r m X' ∗ ⌜derefStep X X' ∧ covered X' bl n⌝ -∗ Φ #()) -∗
        WP (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"dereference")) (Val #())) {{ Φ }}
      : IProp GF) := by
  iloeb as IH
  iintro %K %tx %r %m %X %bl %n %B %Hh %Φ Hw HΦ
  obtain ⟨HB, Hn, Hlive, Hpre, Hfresh⟩ := Hh
  obtain ⟨rn, Hrn⟩ := Option.isSome_iff_exists.1 Hn
  icases wtxW_open K tx r m X $$ Hw with ⟨#Hpk, #Hcore, #Hreg, Hh, Hv, Hst, Hclose⟩
  ihave %Hok := wtxHeap_heapOK tx _ X $$ Hh
  have Hobj := objs_node X.t bl B n rn Hok.2.1 HB Hrn
  have Hnode : X.node bl n = some rn := by simp [WX.node, HB, Hrn]
  icases wtxHeap_setNode tx _ X bl B n rn HB Hrn $$ Hh with ⟨Ho, Hback⟩
  have Hpar : rn.nv.parent' ≠ n := Hok.2.2.2.1 bl B n rn HB Hrn
  rw [decide_eq_true Hlive]
  unfold objOwn
  icases Ho with ⟨Hn, Hins, Hcap, Hws, Hcs, Hcsc, Hkey⟩
  wp_method_call
  wp_call
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  have Hrnl := Hpre.1 bl B n rn HB Hrn Hlive
  have Hrnf := Hfresh bl B n rn HB Hrn Hlive
  wp_auto
  wp_join iprop(∃ k1 : GoSlice, n.[node, go!"key"] ↦ k1 ∗ viewCells wq X.v ∗
      ⌜(rn.nv.key' = slice.nil ∧ k1 = slice.nil) ∨ (rn.nv.key' ≠ slice.nil ∧ k1 ≠ slice.nil)⌝ ∗
      (if rn.nv.key' = slice.nil then emp else k1 ↦*□ rn.key) ∗
      n.[node, go!"pgid"] ↦ rn.nv.pgid' ∗ n_ptr ↦ n)
    with [key Hkey Hv pgid n] as ⟨%k1, key, Hv, %Hk1, Hk1, pgid, n⟩
  · iexists rn.nv.key'
    rw [if_pos Hif]
    iframe
    ipureintro; exact Or.inl ⟨Hif, Hif⟩
  · have Hkne := Hif
    rw [if_pos (show True ∧ rn.nv.key' ≠ slice.nil from ⟨trivial, Hif⟩)]
    ihave %Hkl := srcOwn_len X.v rn.nv.key' rn.ksrc rn.key (Hrnf.2 Hif) $$ Hkey
    have Hkpos : 0 < rn.key.length := by
      rcases Hrnl.2.2.1 with h | h
      · exact absurd h Hif
      · exact h
    try wp_auto
    wp_apply wp_slice_make2 (V := w8) rn.nv.key'.len $$ [] as %kn ⟨Hkn, Hknc⟩
    · ipureintro; exact Hkl.2
    rw [← Hkl.1, show (zero_val w8 : w8) = W8 0 from rfl]
    try wp_auto
    wp_apply wp_copy_kept wq X.v kn rn.nv.key' rn.ksrc rn.key (Hrnf.2 Hif) $$ [Hkn Hv Hkey]
      as %c ⟨Hkn, Hv⟩
    · iframe
    ihave %Hknl := ownSlice_len _ _ _ $$ Hkn
    try wp_auto
    have Hkn0 : 0 < sint.Z kn.len := by
      have h1 := Hknl.1
      have e : sint.Z kn.len = kn.len.toInt := rfl
      simp only [sint.nat] at h1; rw [e]; omega
    have Hkn1 : kn ≠ slice.nil := by
      intro h; rw [h] at Hkn0; simp [slice.nil] at Hkn0
    imod ownSlice_persist kn _ _ $$ Hkn with #Hkn
    wp_if_destruct
    · try wp_auto
      wp_apply hA
      try wp_auto
      wp_join_done
      iexists kn
      rw [if_neg Hkne]
      iframe; iframe #
      ipureintro; exact Or.inr ⟨Hkne, Hkn1⟩
    · try wp_auto
      rw [decide_eq_true (show sint.Z (W64 0) < sint.Z kn.len from Hkn0)]
      wp_apply hA
      try wp_auto
      wp_join_done
      iexists kn
      rw [if_neg Hkne]
      iframe; iframe #
      ipureintro; exact Or.inr ⟨Hkne, Hkn1⟩
  rename_i ia
  ihave %Hinsl := ownSlice_len _ _ _ $$ Hins
  ihave %Hwsl := BigSepL2.bigSepL2_length $$ Hws
  ihave IH2 : (∃ (j : Nat) (insD : List Inode) (wsD : List WEntry) (iv : w64),
      "i" ∷ i_ptr ↦ W64 (j : Int) ∗ "ia" ∷ ia ↦ iv ∗
      "Hins" ∷ rn.nv.inodes' ↦* (insD ++ rn.ins.drop j) ∗
      "HwsD" ∷ ([∗list] it;w ∈ insD;wsD, wOwn X.v true it w) ∗
      "Hws" ∷ ([∗list] it;w ∈ rn.ins.drop j;rn.ws.drop j, wOwn X.v true it w) ∗
      "Hv" ∷ viewCells wq X.v ∗ "inodes" ∷ n.[node, go!"inodes"] ↦ rn.nv.inodes' ∗
      "n" ∷ n_ptr ↦ n ∗
      "%Hj" ∷ ⌜j ≤ rn.ins.length ∧ insD.length = j ∧ wsD.map wDat = (rn.ws.take j).map wDat ∧
        ∀ w ∈ wsD, w.ks = Src.heap ∧ w.vs = Src.heap⌝ : IProp GF)
    $$ [-HΦ Hclose Hback Hst Hcap Hcs Hcsc bucket isLeaf unbalanced spilled parent children key Hk1 pgid]
  · iexists 0, [], [], zero_val w64
    simp only [named, List.drop_zero, List.nil_append]
    iframe
    isplitl []
    · iapply (BigSepL2.bigSepL2_nil (Φ := fun _ it w => wOwn (GF := GF) X.v true it w)).2; itrivial
    ipureintro; simp
  wp_for IH2
  wp_if_destruct
  · have Hlt : j < rn.ins.length := by
      have e : sint.Z (W64 (j : Int)) = j := sint_Z_W64_nat _ (by word)
      rw [e] at Hif; rw [sint_nat_eq] at Hinsl; omega
    obtain ⟨it, Hit_lookup⟩ : ∃ it, rn.ins[j]? = some it :=
      ⟨rn.ins[j], List.getElem?_eq_getElem Hlt⟩
    obtain ⟨w, Hw_lookup⟩ : ∃ w, rn.ws[j]? = some w :=
      ⟨rn.ws[j], List.getElem?_eq_getElem (by omega)⟩
    have Hlk : (insD ++ rn.ins.drop j)[j]? = some it := by
      rw [List.getElem?_append_right (by omega), Hj.2.1, Nat.sub_self, List.getElem?_drop,
        Nat.add_zero, Hit_lookup]
    have Hjz : sint.Z (W64 (j : Int)) = j := sint_Z_W64_nat _ (by word)
    rw [List.drop_eq_getElem_cons Hlt, List.drop_eq_getElem_cons (show j < rn.ws.length by omega)]
    rw [show rn.ins[j] = it from (List.getElem?_eq_some_iff.1 Hit_lookup).2,
      show rn.ws[j] = w from (List.getElem?_eq_some_iff.1 Hw_lookup).2]
    icases Hws with ⟨Hw, Hws⟩
    icases (wOwn_true X.v it w).1 $$ Hw with ⟨%Hfp, Hik, Hiv⟩
    have Hlk' : (insD ++ it :: rn.ins.drop (j + 1))[(j : Int).toNat]? = some it := by
      simp [List.getElem?_append_right, Hj.2.1]
    icases ownSlice_elem_acc (j : Int) it _ _ _ (by omega) Hlk' $$ Hins
      with ⟨Hit, Hsback⟩
    try wp_auto
    rw [if_pos (show 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z rn.nv.inodes'.len
      from ⟨by omega, Hif⟩), Hjz]
    try wp_auto
    rw [if_pos (show 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z rn.nv.inodes'.len
      from ⟨by omega, Hif⟩), Hjz]
    try wp_auto
    have Hwm : w ∈ rn.ws := List.mem_of_getElem? Hw_lookup
    have Hwl := Hrnf.1 w Hwm
    have Hwk := Hrnl.2.1 w Hwm
    ihave %Hkl := srcOwn_len X.v it.key' w.ks w.key Hwl.1 $$ Hik
    ihave %Hvl := srcOwn_len X.v it.value' w.vs w.value Hwl.2 $$ Hiv
    wp_apply hK $$ [$Hit] as Hit
    try wp_auto
    wp_apply wp_slice_make2 (V := w8) it.key'.len $$ [] as %kk ⟨Hkk, Hkkc⟩
    · ipureintro; exact Hkl.2
    rw [← Hkl.1, show (zero_val w8 : w8) = W8 0 from rfl]
    try wp_auto
    wp_apply hK $$ [$Hit] as Hit
    try wp_auto
    wp_apply wp_copy_kept wq X.v kk it.key' w.ks w.key Hwl.1 $$ [Hkk Hv Hik] as %c1 ⟨Hkk, Hv⟩
    · iframe
    ihave %Hkkl := ownSlice_len _ _ _ $$ Hkk
    imod ownSlice_persist kk _ _ $$ Hkk with #Hkk
    try wp_auto
    wp_apply hSK $$ [$Hit] as Hit
    try wp_auto
    wp_apply hK $$ [$Hit] as Hit
    try wp_auto
    have Hkk0 : 0 < sint.Z kk.len := by
      have h1 := Hkkl.1
      have e : sint.Z kk.len = kk.len.toInt := rfl
      rw [sint_nat_eq] at h1; rw [e] at h1 ⊢; omega
    rw [decide_eq_true (show sint.Z (W64 0) < sint.Z kk.len from Hkk0)]
    wp_apply hA
    try wp_auto
    wp_apply hV $$ [$Hit] as Hit
    try wp_auto
    wp_apply wp_slice_make2 (V := w8) it.value'.len $$ [] as %vv ⟨Hvv, Hvvc⟩
    · ipureintro; exact Hvl.2
    rw [← Hvl.1, show (zero_val w8 : w8) = W8 0 from rfl]
    try wp_auto
    wp_apply hV $$ [$Hit] as Hit
    try wp_auto
    wp_apply wp_copy_kept wq X.v vv it.value' w.vs w.value Hwl.2 $$ [Hvv Hv Hiv] as %c2 ⟨Hvv, Hv⟩
    · iframe
    imod ownSlice_persist vv _ _ $$ Hvv with #Hvv
    try wp_auto
    wp_apply hSV $$ [$Hit] as Hit
    try wp_auto
    ihave Hins := Hsback $$ %({ { it with key' := kk } with value' := vv } : Inode) Hit
    wp_for_post
    iframe
    iexists j + 1, insD ++ [({ { it with key' := kk } with value' := vv } : Inode)],
      wsD ++ [{ w with ks := Src.heap, vs := Src.heap }], W64 (j : Int)
    rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by push_cast; word]
    rw [show ((j : Int)).toNat = insD.length by rw [Hj.2.1]; simp, List.set_append_right _ _ (by omega),
      Nat.sub_self, List.set_cons_zero, List.append_assoc, List.singleton_append]
    iframe
    isplitl [Hkk Hvv]
    · iapply (BigSepL2.bigSepL2_cons).2
      isplitl
      · iapply (wOwn_true X.v _ _).2
        isplitr
        · ipureintro; exact Hfp
        unfold srcOwn
        iframe; iframe #
      · iapply (BigSepL2.bigSepL2_nil (Φ := fun _ it w => wOwn (GF := GF) X.v true it w)).2; itrivial
    ipureintro
    refine ⟨by omega, by simp [Hj.2.1], ?_, ?_⟩
    · rw [List.map_append, Hj.2.2.1, List.take_add_one, Hw_lookup]
      simp [wDat]
    · intro w' hw'
      rcases List.mem_append.1 hw' with h | h
      · exact Hj.2.2.2 w' h
      · simp at h; subst h; exact ⟨rfl, rfl⟩
  · have Hje : j = rn.ins.length := by
      have e : sint.Z (W64 (j : Int)) = j := sint_Z_W64_nat _ (by word)
      rw [e] at Hif; rw [sint_nat_eq] at Hinsl; omega
    rw [List.drop_eq_nil_of_le (show rn.ins.length ≤ j by omega),
      List.drop_eq_nil_of_le (show rn.ws.length ≤ j by omega), List.append_nil]
    ihave Hn : (n ↦ ({ rn.nv with key' := k1 } : node) : IProp GF)
      $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    have Hr1 : nodeDerefd rn (rn.derefTo k1 insD wsD) := by
      refine ⟨rfl, ?_, ?_, Hj.2.2.2, ?_, rfl, rfl, rfl, rfl⟩
      · rcases Hk1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [NRec.derefTo, h1, h2]
        · simp [NRec.derefTo, h1, h2]
      · simp only [NRec.derefTo]; rw [Hj.2.2.1, Hje, Hwsl, List.take_length]
      · simp only [NRec.derefTo]; rw [Hj.2.1, Hje]
    ihave Hh := Hback $$ %(rn.derefTo k1 insD wsD) %Hpar [Hn Hins Hcap HwsD Hcs Hcsc Hk1]
    · try simp only [NRec.derefTo]
      iframe
      rcases Hk1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [h2, ne_eq, not_true_eq_false, and_false, ↓reduceIte]; itrivial
      · simp only [h2, h1, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        unfold srcOwn
        iexact Hk1
    have HX1 : derefStep X (X.setNode bl n (rn.derefTo k1 insD wsD)) :=
      derefStep_setNode X bl n B rn _ HB Hrn (Or.inr Hr1)
    ihave Hw := Hclose $$ %(X.setNode bl n (rn.derefTo k1 insD wsD)) [] Hh Hv Hst
    · ipureintro; exact ⟨HX1.1, HX1.2.2.1, by rw [HX1.2.2.2.1, HX1.2.2.2.2.2.1]⟩
    ihave IH3 : (∃ (i : Nat) (Xi : WX) (cv : Loc),
        "i" ∷ i_ptr ↦ W64 (i : Int) ∗ "child" ∷ child_ptr ↦ cv ∗ "Hw" ∷ wtxW K tx r m Xi ∗
        "%Hi" ∷ ⌜i ≤ rn.cs.length ∧ derefStep X Xi ∧
          (∀ B' r', Xi.t.bs !! bl = some B' → B'.ns !! n = some r' → noView r') ∧
          ∀ c ∈ rn.cs.take i, covered Xi bl c⌝ : IProp GF) $$ [i child Hw]
    · iexists 0, X.setNode bl n (rn.derefTo k1 insD wsD), zero_val Loc
      simp only [named]
      iframe
      ipureintro
      refine ⟨by omega, HX1, ?_, by simp⟩
      intro B' r' hB' hr'
      unfold WX.setNode WX.setBkt at hB'
      rw [HB] at hB'
      simp only [GMap.lookup_insert, Option.some.injEq] at hB'
      subst hB'
      simp only [GMap.lookup_insert, Option.some.injEq] at hr'
      subst hr'
      exact noView_derefd Hr1
    wp_for IH3
    obtain ⟨Hil, HXi, HnV, Hcov⟩ := Hi
    obtain ⟨Bi, HBi, Hbs⟩ := optRel_some_l (HB ▸ derefStep_bs HXi bl)
    obtain ⟨ri, Hri, Hrs⟩ := optRel_some_l (Hrn ▸ Hbs.2 n)
    obtain ⟨Hnv, Hcseq, -, -, -, -⟩ := nodeStep_nv Hrs
    have Hlive' : n ∈ Xi.live := by rw [HXi.2.1]; exact Hlive
    have HpreI := derefPre_step HXi Hpre
    have HfreshI := liveFresh_step HXi Hfresh
    have Hch : ri.nv.children' = rn.nv.children' := by rw [Hnv]
    icases wtxW_open K tx r m Xi $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hclose⟩
    icases wtxHeap_node_peek tx _ Xi bl n Bi ri HBi Hri Hlive' $$ Hh with ⟨Ho, Hhb⟩
    unfold objOwn
    icases Ho with ⟨Hn, Hins, Hcap, Hws, Hcs, Hcsc, Hkey⟩
    ihave %Hcsl := ownSlice_len _ _ _ $$ Hcs
    rw [Hcseq, Hch] at Hcsl
    by_cases Hif : sint.Z (W64 (i : Int)) < sint.Z rn.nv.children'.len
    · rw [decide_eq_true Hif]
      simp only [_root_.decide_true, ↓reduceIte]
      have Hlt : i < rn.cs.length := by
        have e : sint.Z (W64 (i : Int)) = i := sint_Z_W64_nat _ (by word)
        rw [e] at Hif; rw [sint_nat_eq] at Hcsl; omega
      obtain ⟨c, Hc_lookup⟩ : ∃ c, rn.cs[i]? = some c := ⟨rn.cs[i], List.getElem?_eq_getElem Hlt⟩
      have Hiz : sint.Z (W64 (i : Int)) = i := sint_Z_W64_nat _ (by word)
      rw [Hcseq, Hch]
      icases ownSlice_elem_acc (i : Int) c _ _ rn.cs (by omega) (by simpa using Hc_lookup) $$ Hcs
        with ⟨Hc, Hcsback⟩
      try wp_auto
      rw [if_pos (show 0 ≤ sint.Z (W64 (i : Int)) ∧ sint.Z (W64 (i : Int)) < sint.Z rn.nv.children'.len
        from ⟨by omega, Hif⟩), Hiz]
      try wp_auto
      ihave Hcs := Hcsback $$ %c Hc
      rw [list_set_lookup_self _ _ _ (by simpa using Hc_lookup)]
      ihave Hh := Hhb $$ [Hn Hins Hcap Hws Hcs Hcsc Hkey]
      · iframe
      ihave Hw := Hclose $$ %Xi [] Hh Hv Hst
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      have Hcm : c ∈ ri.cs := by rw [Hcseq]; exact List.mem_of_getElem? Hc_lookup
      obtain ⟨Hcl, Hcn⟩ := (HpreI.1 bl Bi n ri HBi Hri Hlive').2.2.2 c Hcm
      have Hcpre : Xi.t.bs !! bl = some Bi ∧ (Bi.ns !! c).isSome ∧ c ∈ Xi.live ∧ derefPre Xi ∧
          liveFresh Xi := ⟨HBi, Hcn, Hcl, HpreI, HfreshI⟩
      wp_apply IH $$ %K %tx %r %m %Xi %bl %c %Bi %Hcpre [Hw]
        as %X' ⟨Hw, %HX'⟩
      · iexact Hw
      wp_for_post
      iframe
      iexists i + 1, X', c
      rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by push_cast; word]
      iframe
      ipureintro
      refine ⟨by omega, derefStep_trans _ _ _ HXi HX'.1, ?_, ?_⟩
      · intro B' r' hB' hr'
        obtain ⟨B2, hB2, hs2⟩ := optRel_some_r (hB' ▸ derefStep_bs HX'.1 bl)
        obtain ⟨r2, hr2, hrs2⟩ := optRel_some_r (hr' ▸ hs2.2 n)
        exact noView_step hrs2 (HnV B2 r2 hB2 hr2)
      · intro c' hc'
        rw [List.take_add_one, Hc_lookup] at hc'
        rcases List.mem_append.1 hc' with h | h
        · exact covered_step HX'.1 (Hcov c' h)
        · simp at h; subst h; exact HX'.2
    · rw [decide_eq_false Hif]
      simp only [_root_.decide_true, _root_.decide_false, ↓reduceIte]
      have Hie : i = rn.cs.length := by
        have e : sint.Z (W64 (i : Int)) = i := sint_Z_W64_nat _ (by word)
        rw [e] at Hif; rw [sint_nat_eq] at Hcsl; omega
      icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, -⟩
      iStructNamed Hn
      have Hbk : ri.nv.bucket' = bl := by rw [Hnv]; exact Hrnl.1
      simp only [Bool.false_eq_true, ↓reduceIte]
      try wp_auto
      rw [Hbk]
      ihave Hn : (n ↦ ri.nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        rw [Hbk]
        iframe
      ihave Hh := Hhb $$ [Hn Hins Hcap Hws Hcs Hcsc Hkey]
      · iframe
      ihave %HokI := wtxHeap_heapOK tx _ Xi $$ Hh
      have HblL : bl ∈ Xi.liveB := (HpreI.2.2.1 bl Bi HBi).1
      icases wtxHeap_bkt_peek tx _ Xi bl Bi HBi HblL $$ Hh with ⟨Hb, Hbb⟩
      unfold objOwn
      icases Hb with ⟨Hb1, Hbtx, Hb3⟩
      have Htx : Bi.bv.tx' = tx := (HokI.2.2.1 bl Bi HBi).1
      ihave Hbtx2 : (∃ dq : DFrac, bl.[Bucket, go!"tx"] ↦{dq} tx ∗
          (bl.[Bucket, go!"tx"] ↦{dq} tx -∗
            (if bl = Bi.bv.tx'.[Tx, go!"root"] then bl.[Bucket, go!"tx"] ↦ Bi.bv.tx'
             else bl.[Bucket, go!"tx"] ↦□ Bi.bv.tx')) : IProp GF) $$ [Hbtx]
      · rw [Htx]
        by_cases hroot : bl = tx.[Tx, go!"root"]
        · rw [if_pos hroot]; iexists DFrac.own 1; iframe; iintro H; iexact H
        · rw [if_neg hroot]
          icases Hbtx with #Hbtx
          iexists DFrac.discard
          isplitr
          · iexact Hbtx
          iintro -; iexact Hbtx
      icases Hbtx2 with ⟨%dqt, Hbtx, Hbtxb⟩
      try wp_auto
      wp_apply hInc K tx r m 1 (W64 1) $$ [Hst] as %nn Hst
      · iframe; iframe #
      try wp_auto
      ihave Hbtx := Hbtxb $$ Hbtx
      ihave Hh := Hbb $$ [Hb1 Hbtx Hb3]
      · dsimp only
        iframe
      ihave Hw := Hclose $$ %Xi [] Hh Hv Hst
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iapply HΦ
      iframe
      ipureintro
      refine ⟨HXi, ?_⟩
      intro B' d r' hB' hd hr'
      rw [HBi] at hB'
      cases hB'
      cases hd with
      | self => exact HnV Bi r' HBi hr'
      | child _ c _ r0 hr0 hc hcd =>
        rw [Hri] at hr0
        cases hr0
        have hc' : c ∈ rn.cs.take i := by rw [Hie, List.take_length, ← Hcseq]; exact hc
        exact Hcov c hc' Bi d r' HBi hcd hr'

theorem node.dereference.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.Inode.Value.spec (GF := GF) (hG := hG))
    (hSK : internal.common.Inode.SetKey.spec (GF := GF) (hG := hG))
    (hSV : internal.common.Inode.SetValue.spec (GF := GF) (hG := hG))
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncNodeDeref.spec (GF := GF) (hG := hG)) :
    node.dereference.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl n B HB Hn Hl Hpre Hfresh
  have Hp : X.t.bs !! bl = some B ∧ (B.ns !! n).isSome ∧ n ∈ X.live ∧ derefPre X ∧
    liveFresh X := ⟨HB, Hn, Hl, Hpre, Hfresh⟩
  iintro %Φ Hw HΦ
  iapply (node.dereference.wp_aux hK hV hSK hSV hA hInc) $$ %K %tx %r %m %X %bl %n %B %Hp Hw
  inext
  iintro %X' HX'
  iapply HΦ
  iexists X'
  iexact HX'

end proof

end bbolt
end EtcdGrove
end Perennial
