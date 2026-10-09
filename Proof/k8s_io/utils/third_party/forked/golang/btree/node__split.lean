module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__split
public import Spec.k8s_io.utils.third_party.forked.golang.btree.copyOnWriteContext__newNode
public import Spec.k8s_io.utils.third_party.forked.golang.btree.items__truncate
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

theorem node.split.wp_proof
    (wp_newNode : copyOnWriteContext.newNode.spec (GF := GF) (hG := hG))
    (wp_truncate : items.truncate.spec (GF := GF) (hG := hG)) :
    node.split.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less n is cs i e Hi He Hcs
  wp_start as ⟨#Hcow, Hn⟩
  unfold ownedNode nodeShallow nodeFields
  simp only [Tree.items_node, Tree.children_node]
  icases Hn with ⟨%ps, ⟨%isl, %csl, ⟨%Hnn, Hfi, Hfc, Hfw⟩, Hisl, Hicap, Hcsl, Hccap⟩, Hch⟩
  ihave %Hli := ownSlice_len _ _ _ $$ Hisl
  ihave %Hlc := ownSlice_len _ _ _ $$ Hcsl
  ihave %Hwi := ownSlice_wf _ _ _ $$ Hisl
  ihave %Hwc := ownSlice_wf _ _ _ $$ Hcsl
  ihave %Hpl := ownNodes_length _ _ _ _ _ _ _ $$ Hch
  simp only [List.length_map] at Hli
  have hb : sint.nat i < is.length := by
    rcases List.getElem?_eq_some_iff.1 He with ⟨h, _⟩; exact h
  have He1 : (is.map Prod.fst)[sint.nat i]? = some e.1 := by simp [He]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi, by word⟩)]
  wp_apply wp_load_slice_index isl (sint.Z i) _ _ e.1 Hi $$ [Hisl] as Hisl
  · iframe; ipureintro; exact He1
  wp_apply wp_newNode o c f less $$ [$Hcow] as %nx Hnx
  unfold nodeShallow nodeFields
  icases Hnx with ⟨%nisl, %ncsl, ⟨%Hnxn, Hni, Hnc, Hnw⟩, Hnisl, Hnicap, Hncsl, Hnccap⟩
  simp only [List.map_nil]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
  icases (ownSlice_slice (i + W64 1) isl.len isl _ _ ⟨by word, by word, by word⟩).1 $$ Hisl
    with ⟨Hs1, Hs2, Hs3⟩
  wp_apply wp_slice_append $$ [$Hnisl $Hnicap $Hs2] as %nisl' ⟨Hnisl, Hnicap, Hs2⟩
  ihave Hisl := (ownSlice_slice (i + W64 1) isl.len isl _ _ ⟨by word, by word, by word⟩).2
    $$ [$Hs1 $Hs2 $Hs3]
  wp_apply wp_truncate _ isl _ i Hi (by simp; word) $$ [$Hfi $Hisl $Hicap] as %isl' ⟨Hfi, Hisl, Hicap⟩
  have hsub : subslice (sint.nat (i + W64 1)) (sint.nat isl.len) (List.map Prod.fst is) =
      List.map Prod.fst (is.drop (sint.nat i + 1)) := by
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, ← Hli.1]
    simp only [subslice, List.map_drop]
    rw [List.take_of_length_le (by simp)]
  rw [hsub, List.nil_append, ← List.map_take]
  wp_if_destruct
  · -- an internal node
    have hcs : cs.length = is.length + 1 := by
      rcases Hcs with h | h
      · exfalso; subst h
        have : ps = [] := List.eq_nil_of_length_eq_zero (by simpa using Hpl)
        subst this; simp at Hlc; word
      · exact h
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
    icases (ownSlice_slice (i + W64 1) csl.len csl _ _ ⟨by word, by word, by word⟩).1 $$ Hcsl
      with ⟨Hc1, Hc2, Hc3⟩
    wp_apply wp_slice_append $$ [$Hncsl $Hnccap $Hc2] as %ncsl' ⟨Hncsl, Hnccap, Hc2⟩
    ihave Hcsl := (ownSlice_slice (i + W64 1) csl.len csl _ _ ⟨by word, by word, by word⟩).2
      $$ [$Hc1 $Hc2 $Hc3]
    wp_apply wp_truncate _ csl _ (i + W64 1) (by word) (by word) $$ [$Hfc $Hcsl $Hccap]
      as %csl' ⟨Hfc, Hcsl, Hccap⟩
    have hsub2 : subslice (sint.nat (i + W64 1)) (sint.nat csl.len) ps =
        ps.drop (sint.nat i + 1) := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, ← Hlc.1]
      simp only [subslice]
      rw [List.take_of_length_le (by simp)]
    rw [hsub2, List.nil_append, show sint.nat (i + W64 1) = sint.nat i + 1 by word]
    icases ownNodes_take_drop o c f less _ (sint.nat i + 1) ps cs Hpl $$ Hch with ⟨Hch1, Hch2⟩
    iapply HΦ
    isplitl [Hfi Hfc Hfw Hisl Hicap Hcsl Hccap Hch1]
    · iexists _
      iframe Hch1
      iexists isl', csl'
      iframe
      ipureintro; exact Hnn
    · iexists _
      iframe Hch2
      iexists nisl', ncsl'
      iframe
      ipureintro; exact Hnxn
  · -- a leaf
    have hc0 : ps = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    subst hc0
    have hcs0 : cs = [] := by
      apply List.eq_nil_of_length_eq_zero; simp at Hpl; omega
    subst hcs0
    iapply HΦ
    simp only [List.take_nil, List.drop_nil, ownNodes_nil]
    isplitl [Hfi Hfc Hfw Hisl Hicap Hcsl Hccap]
    · iexists []
      isplitl
      · iexists isl', csl
        iframe
        ipureintro; exact Hnn
      · rw [ownNodes_nil]; itrivial
    · iexists []
      isplitl
      · iexists nisl', ncsl
        iframe
        ipureintro; exact Hnxn
      · rw [ownNodes_nil]; itrivial

end proof

end btree
end EtcdGrove
end Perennial
