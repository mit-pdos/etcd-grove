/-
The body of `op.toTxnRequest()`, shared by the proofs of `Op.toTxnRequest` and `Op.toRequestOp`
(whose nested case is `toTxnRequest`'s body at the subtrees, by induction on the tree; a nested
transaction's requests are `toRequestOp`'s): `toTxnRequest_core` proves the body over the triple of
`toRequestOp` at the transaction's subtrees (`Op.toRequestOp.specAt`). Lean-first (no Rocq
counterpart; `notes/txn-nested.md`, S2, S4).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__toTxnRequest
public import Spec.go_etcd_io.etcd.client.v3.Op__toRequestOp
public import Spec.go_etcd_io.etcd.client.v3.Cmp__Clone
public import Spec.go_etcd_io.etcd.client.v3.Cmp__GetCompare
public import Proof.go_etcd_io.etcd.client.v3.InvTxnBuilder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.toRequestOp()`'s triple at the tree `t` (`Op.toRequestOp.spec` at one tree). -/
abbrev Op.toRequestOp.specAt (opv : go_etcd_io.etcd.client.v3.Op) (t : OpT) : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opTAtC false opv t ∗
      ⌜∀ o ∈ t.leaves, (o.t = W64 1 ∨ o.t = W64 2 ∨ o.t = W64 3) ∧
        (o.t = W64 2 → o.ignoreValue = true → o.val = [])⌝ }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"toRequestOp")) (Val #()))
  {{ (p : Loc), RET #p; reqOpAt p (OpT.wire t) }}

theorem set_append_replicate {α : Type} (ps : List α) (m : Nat) (z p : α) (hm : 0 < m) :
    (ps ++ List.replicate m z).set ps.length p = (ps ++ [p]) ++ List.replicate (m - 1) z := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp [List.set_append_right, List.replicate_succ]

/-- **`toTxnRequest`'s body** over `toRequestOp`'s triple at the subtrees (`hrec`). -/
theorem toTxnRequest_core (wp_Clone : Cmp.Clone.spec (GF := GF) (hG := hG))
    (wp_GetCompare : Cmp.GetCompare.spec (GF := GF) (hG := hG))
    (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull) (cs : List CmpModel) (ts es : List OpT)
    (hrec : ∀ t ∈ ts ++ es, ∀ v, Op.toRequestOp.specAt (GF := GF) (hG := hG) v t) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      opTAtC false opv (.txn o cs ts es) ∗
      ⌜∀ x ∈ (OpT.txn o cs ts es).leaves, (x.t = W64 1 ∨ x.t = W64 2 ∨ x.t = W64 3) ∧
        (x.t = W64 2 → x.ignoreValue = true → x.val = [])⌝ }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"toTxnRequest")) (Val #()))
  {{ (r : Loc), RET #r; ⌜r ≠ null⌝ ∗ txnReqFieldsAt r cs (OpT.wireL ts) (OpT.wireL es) }} := by
  wp_start as ⟨#Hat, HlvI⟩
  icases HlvI with %Hlv
  have Hlv' := Hlv
  iunfold opTAtC at Hat
  icases Hat with ⟨#Hf, %Ht, #Hcs, %tvs, %evs, #Htv, #Hev, -, #Htl, #Hel⟩
  ihave %Htll := opListAtC_length false tvs ts $$ Htl
  ihave %Hsll := ownSlice_len $$ Htv
  iapply wp_fupd
  wp_auto
  wp_apply (wp_slice_make2 (V := Loc) opv.thenOps'.len) as %tsl ⟨Htsl, Htcap⟩
  · ipureintro; word
  rename_i ui_ptr
  irename : (ui_ptr ↦ zero_val w64 : IProp GF) => ui
  ihave %Htsll := ownSlice_len $$ Htsl
  simp only [List.length_replicate] at Htsll
  ihave IH : iprop(∃ (k : w64) (ov : go_etcd_io.etcd.client.v3.Op) (uk : w64) (ps : List Loc),
      "i" ∷ i_ptr ↦ k ∗ "tOp" ∷ tOp_ptr ↦ ov ∗ "ui" ∷ ui_ptr ↦ uk ∗
      "Htsl" ∷ tsl ↦* (ps ++ List.replicate (sint.nat opv.thenOps'.len - ps.length) (zero_val Loc)) ∗
      "#Hps" ∷ reqOpsAt ps (OpT.wireL (ts.take (sint.nat k))) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (tvs.length : Int) ∧ ps.length = sint.nat k⌝)
      $$ [i tOp ui Htsl]
  · iexists W64 0, _, _, []
    simp only [named, List.nil_append, List.length_nil, Nat.sub_zero]
    iframe
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero]
    isplitl []
    · rw [show OpT.wireL ([] : List OpT) = [] from rfl]; iapply reqOpsAt_nil
    ipureintro; exact ⟨by word, by word, by first | trivial | rfl | simp⟩
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z k < sint.Z opv.thenOps'.len := by simpa using Hif
    have Hlt : sint.nat k < tvs.length := by rw [Hsll.1]; word
    obtain ⟨v, Hvi⟩ : ∃ v, tvs[sint.nat k]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨t, Hti⟩ : ∃ t, ts[sint.nat k]? = some t :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Htll]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z opv.thenOps'.len := ⟨Hk.1, Hif'⟩
    icases ownSlice_elem_acc (sint.Z k) v opv.thenOps' DFrac.discard tvs Hk.1 Hvi $$ Htv
      with ⟨#Hve0, -⟩
    ihave ⟨#Hvt, -⟩ := opListAtC_get false tvs ts _ v t Hvi Hti $$ Htl
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_auto
    wp_method_call
    wp_auto
    have htm : t ∈ ts := List.mem_of_getElem? Hti
    wp_apply (hrec t (List.mem_append_left _ htm) v) $$ [] as %p #Hp
    · iframe #
      ipureintro
      intro x hx
      exact Hlv x (by simp only [OpT.leaves, List.mem_append]; exact Or.inl (mem_leavesL htm hx))
    have Hbt : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z tsl.len := ⟨Hk.1, by word⟩
    simp only [Hbt, _root_.and_self, ↓reduceIte]
    have Hpl : ps.length < sint.nat opv.thenOps'.len := by word
    wp_apply wp_store_slice_index tsl (sint.Z k) _ p $$ [$Htsl] as Htsl
    · ipureintro; simp only [List.length_append, List.length_replicate]; constructor <;> word
    rw [show (sint.Z k).toNat = ps.length by word,
      set_append_replicate ps _ (zero_val Loc) p (by omega)]
    wp_for_post
    iframe
    iexists k + W64 1, v, k, ps ++ [p]
    simp only [named]
    rw [show sint.nat opv.thenOps'.len - ps.length - 1 = sint.nat opv.thenOps'.len - (ps ++ [p]).length
      by simp; omega]
    iframe
    isplitl []
    · rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_add_one, Hti]
      simp only [Option.toList_some, OpT.wireL_map, List.map_append, List.map_cons, List.map_nil]
      iapply reqOpsAt_snoc
      iframe #
    ipureintro; simp only [List.length_append, List.length_singleton]; refine ⟨by word, by word, by word⟩
  · have Hke : sint.nat k = ts.length := by rw [← Htll]; word
    rw [Hke, List.take_length]
    rw [show sint.nat opv.thenOps'.len - ps.length = 0 by have := Hk.2.2; omega, List.replicate_zero, List.append_nil]
    clear Hif Hk
    ihave %Hell := opListAtC_length false evs es $$ Hel
    ihave %Hsel := ownSlice_len $$ Hev
    wp_apply (wp_slice_make2 (V := Loc) opv.elseOps'.len) as %esl ⟨Hesl, Hecap⟩
    · ipureintro; word
    rename_i ue_ptr
    irename : (ue_ptr ↦ zero_val w64 : IProp GF) => ue
    ihave %Hesll := ownSlice_len $$ Hesl
    simp only [List.length_replicate] at Hesll
    ihave IH : iprop(∃ (j : w64) (ov : go_etcd_io.etcd.client.v3.Op) (uk : w64) (qs : List Loc),
        "i" ∷ i_ptr ↦ j ∗ "eOp" ∷ eOp_ptr ↦ ov ∗ "ue" ∷ ue_ptr ↦ uk ∗
        "Hesl" ∷ esl ↦* (qs ++ List.replicate (sint.nat opv.elseOps'.len - qs.length) (zero_val Loc)) ∗
        "#Hes" ∷ reqOpsAt qs (OpT.wireL (es.take (sint.nat j))) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (evs.length : Int) ∧ qs.length = sint.nat j⌝)
        $$ [i eOp ue Hesl]
    · iexists W64 0, _, _, []
      simp only [named, List.nil_append, List.length_nil, Nat.sub_zero]
      iframe
      simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero]
      isplitl []
      · rw [show OpT.wireL ([] : List OpT) = [] from rfl]; iapply reqOpsAt_nil
      ipureintro; exact ⟨by word, by word, by first | trivial | rfl | simp⟩
    wp_for IH
    wp_if_destruct
    · have Hif' : sint.Z j < sint.Z opv.elseOps'.len := by simpa using Hif
      have Hlt : sint.nat j < evs.length := by rw [Hsel.1]; word
      obtain ⟨v, Hvi⟩ : ∃ v, evs[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨t, Hei⟩ : ∃ t, es[sint.nat j]? = some t :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hell]; exact Hlt)⟩
      have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z opv.elseOps'.len := ⟨Hj.1, Hif'⟩
      icases ownSlice_elem_acc (sint.Z j) v opv.elseOps' DFrac.discard evs Hj.1 Hvi $$ Hev
        with ⟨#Hve0, -⟩
      ihave ⟨#Hvt, -⟩ := opListAtC_get false evs es _ v t Hvi Hei $$ Hel
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_method_call
      wp_auto
      have hem : t ∈ es := List.mem_of_getElem? Hei
      wp_apply (hrec t (List.mem_append_right _ hem) v) $$ [] as %p #Hp
      · iframe #
        ipureintro
        intro x hx
        exact Hlv x (by simp only [OpT.leaves, List.mem_append]; exact Or.inr (mem_leavesL hem hx))
      have Hbt : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z esl.len := ⟨Hj.1, by word⟩
      simp only [Hbt, _root_.and_self, ↓reduceIte]
      have Hpl : qs.length < sint.nat opv.elseOps'.len := by word
      wp_apply wp_store_slice_index esl (sint.Z j) _ p $$ [$Hesl] as Hesl
      · ipureintro; simp only [List.length_append, List.length_replicate]; constructor <;> word
      rw [show (sint.Z j).toNat = qs.length by word,
        set_append_replicate qs _ (zero_val Loc) p (by omega)]
      wp_for_post
      iframe
      iexists j + W64 1, v, j, qs ++ [p]
      simp only [named]
      rw [show sint.nat opv.elseOps'.len - qs.length - 1 = sint.nat opv.elseOps'.len - (qs ++ [p]).length
        by simp; omega]
      iframe
      isplitl []
      · rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hei]
        simp only [Option.toList_some, OpT.wireL_map, List.map_append, List.map_cons, List.map_nil]
        iapply reqOpsAt_snoc
        iframe #
      ipureintro; simp only [List.length_append, List.length_singleton]; refine ⟨by word, by word, by word⟩
    · have Hje : sint.nat j = es.length := by rw [← Hell]; word
      rw [Hje, List.take_length]
      rw [show sint.nat opv.elseOps'.len - qs.length = 0 by have := Hj.2.2; omega, List.replicate_zero, List.append_nil]
      clear Hif Hj
      iunfold cmpsAt at Hcs
      icases Hcs with ⟨%cvs, #Hcss, %Hcl, #Hcsa⟩
      ihave %Hcsl := ownSlice_len $$ Hcss
      wp_apply (wp_slice_make2 (V := Loc) opv.cmps'.len) as %csl ⟨Hcsl, Hccap⟩
      · ipureintro; word
      rename_i uc_ptr
      irename : (uc_ptr ↦ zero_val w64 : IProp GF) => uc
      ihave %Hcsll := ownSlice_len $$ Hcsl
      simp only [List.length_replicate] at Hcsll
      ihave IH : iprop(∃ (k : w64) (uk : w64) (rs : List Loc),
          "i" ∷ i_ptr ↦ k ∗ "uc" ∷ uc_ptr ↦ uk ∗
          "Hcsl" ∷ csl ↦* (rs ++ List.replicate (sint.nat opv.cmps'.len - rs.length) (zero_val Loc)) ∗
          "#Hrs" ∷ comparesAt rs (cs.take (sint.nat k)) ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (cvs.length : Int) ∧ rs.length = sint.nat k⌝)
          $$ [i uc Hcsl]
      · iexists W64 0, _, []
        simp only [named, List.nil_append, List.length_nil, Nat.sub_zero]
        iframe
        simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero]
        isplitl []
        · iapply comparesAt_nil
        ipureintro; exact ⟨by word, by word, by first | trivial | rfl | simp⟩
      wp_for IH
      wp_if_destruct
      · have Hif' : sint.Z k < sint.Z opv.cmps'.len := by simpa using Hif
        have Hlt : sint.nat k < cvs.length := by rw [Hcsl.1]; word
        obtain ⟨c, Hci⟩ : ∃ c, cvs[sint.nat k]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
        obtain ⟨m, Hmi⟩ : ∃ m, cs[sint.nat k]? = some m :=
          ⟨_, List.getElem?_eq_getElem (by rw [← Hcl]; exact Hlt)⟩
        have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z opv.cmps'.len := ⟨Hk.1, Hif'⟩
        icases ownSlice_elem_acc (sint.Z k) c opv.cmps' DFrac.discard cvs Hk.1 Hci $$ Hcss
          with ⟨#Hce0, -⟩
        ihave #Hcm := Hcsa $$ %(sint.nat k) %c %m %Hci %Hmi
        simp only [Hbnd, _root_.and_self, ↓reduceIte]
        wp_auto
        simp only [Hbnd, _root_.and_self, ↓reduceIte]
        wp_auto
        wp_apply wp_Clone $$ [$Hce0 $Hcm] as %c' ⟨-, %Hc'n, Hcown⟩
        iunfold compareOwn at Hcown
        icases Hcown with ⟨%ksl, %esl', %u, Hres, #Htgt, #Hkey, #Hks, Hre, #Hesl', Htu, #Hu⟩
        ipersist Hres; ipersist Hre; ipersist Htu
        (try wp_auto)
        wp_apply wp_GetCompare $$ [$cmp]
        · ipureintro; exact Hc'n
        iintro -
        wp_auto
        have Hbt : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z csl.len := ⟨Hk.1, by word⟩
        simp only [Hbt, _root_.and_self, ↓reduceIte]
        have Hrl : rs.length < sint.nat opv.cmps'.len := by word
        wp_apply wp_store_slice_index csl (sint.Z k) _ c'.c' $$ [$Hcsl] as Hcsl
        · ipureintro; simp only [List.length_append, List.length_replicate]; constructor <;> word
        rw [show (sint.Z k).toNat = rs.length by word,
          set_append_replicate rs _ (zero_val Loc) c'.c' (by omega)]
        wp_for_post
        iframe
        iexists k + W64 1, k, rs ++ [c'.c']
        simp only [named]
        rw [show sint.nat opv.cmps'.len - rs.length - 1 = sint.nat opv.cmps'.len - (rs ++ [c'.c']).length
          by simp; omega]
        iframe
        ihave #Hcmp : compareAt (GF := GF) c'.c' m $$ []
        · unfold compareAt
          iexists ksl, esl', u
          iframe #
        isplitl []
        · rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_add_one, Hmi]
          simp only [Option.toList_some]
          iapply comparesAt_snoc
          iframe #
          ipureintro; exact Hc'n
        ipureintro; simp only [List.length_append, List.length_singleton]; refine ⟨by word, by word, by word⟩
      · have Hke' : sint.nat k = cs.length := by rw [← Hcl]; word
        rw [Hke', List.take_length]
        rw [show sint.nat opv.cmps'.len - rs.length = 0 by have := Hk.2.2; omega, List.replicate_zero,
          List.append_nil]
        irename «$r0» => Hr
        ihave %Hrn := typedPointsto_not_null _ _ _ $$ Hr
        iStructNamed Hr
        ipersist Compare; ipersist Success; ipersist Failure
        ipersist Htsl; ipersist Hesl; ipersist Hcsl
        imodintro
        iapply HΦ
        isplitl []
        · ipureintro; exact Hrn
        unfold txnReqFieldsAt
        iexists csl, tsl, esl, rs, ps, qs
        iframe #

end proof

end EtcdGrove
end Perennial
