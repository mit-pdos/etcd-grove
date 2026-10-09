module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__mutableFor
public import Spec.k8s_io.utils.third_party.forked.golang.btree.copyOnWriteContext__newNode
public import Proof.k8s_io.utils.third_party.forked.golang.btree.NodeLemmas
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Lemmas.Struct

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem node.mutableFor.wp_proof
    (wp_newNode : copyOnWriteContext.newNode.spec (GF := GF) (hG := hG)) :
    node.mutableFor.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less n t
  obtain ⟨is, cs⟩ := t
  wp_start as ⟨#Hcow, Hn⟩
  wp_auto
  icases (ownNode_unfold o c f less _ n _).1 $$ Hn with (Hown | Hfr)
  · unfold ownedNode nodeShallow nodeFields
    icases Hown with ⟨%ps, ⟨%isl, %csl, ⟨%Hnn, Hi, Hc, Hw⟩, Hisl⟩, Hch⟩
    wp_auto
    iapply HΦ
    iexists ps
    iframe Hch
    iexists isl, csl
    iframe
    ipureintro; exact Hnn
  · rw [frozen_node]; unfold nodeFields
    icases Hfr with ⟨%isl, %csl, %cw, %ps, ⟨%Hnn, #Hi, #Hc, #Hw⟩, %Hne, #Hcw, #Hisl, #Hcsl, #Hch⟩
    wp_auto
    wp_if_destruct
    · exact absurd Hif Hne
    wp_apply wp_newNode o c f less $$ [$Hcow] as %out Hout
    unfold nodeShallow nodeFields
    icases Hout with ⟨%oisl, %ocsl, ⟨%Honn, Hoi, Hoc, How⟩, Hoisl, Hoicap, Hocsl, Hoccap⟩
    ihave %Hlo := ownSlice_len _ _ _ $$ Hoisl
    ihave %Hlo2 := ownSlice_len _ _ _ $$ Hocsl
    ihave %Hwi := ownSlice_wf _ _ _ $$ Hisl
    ihave %Hwc := ownSlice_wf _ _ _ $$ Hcsl
    ihave %Hli := ownSlice_len _ _ _ $$ Hisl
    ihave %Hlc := ownSlice_len _ _ _ $$ Hcsl
    ihave %Hwoi := ownSliceCap_wf _ _ $$ Hoicap
    ihave %Hwoc := ownSliceCap_wf _ _ $$ Hoccap
    wp_auto
    wp_join iprop(∃ (sl : GoSlice) (vs : List V),
        n_ptr ↦ n ∗ out_ptr ↦ out ∗ out.[node V, go!"items"] ↦ sl ∗ sl ↦* vs ∗ ownSliceCap V sl (DFrac.own 1) ∗
        ⌜vs.length = sint.nat isl.len⌝)
      with [n out Hoi Hoisl Hoicap] as ⟨%sl1, %vs1, n, out, Hoi, Hs1, Hs1cap, %Hvs1⟩
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, Hif⟩)]
      wp_auto
      icases ownSlice_slice_into_capacity (W64 0) isl.len oisl _ $$ [Hoisl Hoicap]
        with ⟨%vc, -, Hs, Hcap⟩
      · iframe; ipureintro; simp at Hlo; refine ⟨by word, by word, by word, Hif⟩
      ihave %Hl := ownSlice_len _ _ _ $$ Hs
      wp_join_done
      iexists _, _
      iframe
      ipureintro; simp only [slice.slice] at Hl; word
    · wp_apply wp_slice_make3 (V := V) isl.len isl.cap Hwi as %ns ⟨Hns, Hnscap, -⟩
      wp_join_done
      iexists _, _
      iframe
      ipureintro; simp
    wp_apply wp_slice_copy sl1 vs1 isl _ DFrac.discard $$ [Hs1 Hisl] as %k1 ⟨-, Hs1, -⟩
    · iframe; iexact Hisl
    rw [List.drop_of_length_le (by rw [Hvs1, Hli.1]; exact Nat.le_refl _), List.append_nil]
    wp_join iprop(∃ (sl : GoSlice) (vs : List Loc),
        n_ptr ↦ n ∗ out_ptr ↦ out ∗ out.[node V, go!"children"] ↦ sl ∗ sl ↦* vs ∗
        ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜vs.length = sint.nat csl.len⌝)
      with [n out Hoc Hocsl Hoccap] as ⟨%sl2, %vs2, n, out, Hoc, Hs2, Hs2cap, %Hvs2⟩
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, Hif⟩)]
      wp_auto
      icases ownSlice_slice_into_capacity (W64 0) csl.len ocsl _ $$ [Hocsl Hoccap]
        with ⟨%vc, -, Hs, Hcap⟩
      · iframe; ipureintro; simp at Hlo2; refine ⟨by word, by word, by word, Hif⟩
      ihave %Hl := ownSlice_len _ _ _ $$ Hs
      wp_join_done
      iexists _, _
      iframe
      ipureintro; simp only [slice.slice] at Hl; word
    · wp_apply wp_slice_make3 (V := Loc) csl.len csl.cap Hwc as %ns ⟨Hns, Hnscap, -⟩
      wp_join_done
      iexists _, _
      iframe
      ipureintro; simp
    wp_apply wp_slice_copy sl2 vs2 csl _ DFrac.discard $$ [Hs2 Hcsl] as %k2 ⟨-, Hs2, -⟩
    · iframe; iexact Hcsl
    rw [List.drop_of_length_le (by rw [Hvs2, Hlc.1]; exact Nat.le_refl _), List.append_nil]
    wp_auto
    iapply HΦ
    unfold ownedNode nodeShallow nodeFields
    simp only [Tree.items_node, Tree.children_node]
    iexists ps
    isplitl [Hoi Hoc How Hs1 Hs1cap Hs2 Hs2cap]
    · iexists sl1, sl2
      rw [List.take_of_length_le (by rw [Hvs1, Hli.1]; exact Nat.le_refl _),
        List.take_of_length_le (by rw [Hvs2, Hlc.1]; exact Nat.le_refl _)]
      iframe
      ipureintro; exact Honn
    · iapply ownNodes_of_frozenList $$ Hch

end proof

end btree
end EtcdGrove
end Perennial
