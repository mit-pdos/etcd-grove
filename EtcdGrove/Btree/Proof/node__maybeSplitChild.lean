import EtcdGrove.Btree.Spec.node__maybeSplitChild
import EtcdGrove.Btree.Spec.node__mutableChild
import EtcdGrove.Btree.Spec.node__split
import EtcdGrove.Btree.Spec.items__insertAt
import EtcdGrove.Btree.NodeLemmas
import EtcdGrove.Btree.Lemmas.Struct

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

theorem node.maybeSplitChild.wp_proof
    (wp_mutableChild : node.mutableChild.spec (GF := GF) (hG := hG))
    (wp_split : node.split.spec (GF := GF) (hG := hG))
    (wp_insertAt : items.insertAt.spec (GF := GF) (hG := hG)) :
    node.maybeSplitChild.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less n is cs i maxItems cis ccs Hi Hil Hc Hccs Hmax
  wp_start as ⟨#Hcow, Hn⟩
  unfold ownedNode
  simp only [Tree.items_node, Tree.children_node]
  icases Hn with ⟨%ps, Hsh, Hch⟩
  ihave %Hpl := ownNodes_length _ _ _ _ _ _ _ $$ Hch
  have hb : sint.nat i < ps.length := by
    rcases List.getElem?_eq_some_iff.1 Hc with ⟨h, _⟩; omega
  list_elem ps (sint.nat i) as p
  icases (ownNodes_extract o c f less _ ps cs (sint.nat i) p _ Hp_lookup Hc).1 $$ Hch
    with ⟨Hc, Hch⟩
  icases ownNode_items_acc o c f less _ p cis ccs $$ Hc with ⟨%cisl, %dq', Hci, %Hcl, Hcclose⟩
  unfold nodeShallow nodeFields
  icases Hsh with ⟨%isl, %csl, ⟨%Hnn, Hfi, Hfc, Hfw⟩, Hisl, Hicap, Hcsl, Hccap⟩
  ihave %Hlc := ownSlice_len _ _ _ $$ Hcsl
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi, by word⟩)]
  wp_apply wp_load_slice_index csl (sint.Z i) ps _ p Hi $$ [Hcsl] as Hcsl
  · iframe; ipureintro; exact Hp_lookup
  ihave Hc := Hcclose $$ Hci
  have hcsl : cs.length = ps.length := Hpl.symm
  wp_if_destruct
  · -- not full
    iapply HΦ
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    isplitr
    · ipureintro; rfl
    iexists ps
    isplitr [Hch Hc]
    · iexists isl, csl
      iframe
      ipureintro; exact Hnn
    · iapply (ownNodes_extract o c f less _ ps cs (sint.nat i) p _ Hp_lookup Hc).2
      iframe
  · -- full: split it
    have hfull : sint.nat maxItems ≤ cis.length := by word
    wp_apply wp_mutableChild o c f less n is ps i p _ Hi Hp_lookup $$ [$Hcow Hfi Hfc Hfw Hisl Hicap Hcsl Hccap $Hc]
      as %c' ⟨Hsh, Hc'⟩
    · unfold nodeShallow nodeFields
      iexists isl, csl
      iframe
      ipureintro; exact Hnn
    list_elem cis (sint.nat maxItems / 2) as e
    have hdiv : sint.nat (BitVec.sdiv maxItems (W64 2)) = sint.nat maxItems / 2 := by word
    wp_apply wp_split o c f less c' cis ccs (BitVec.sdiv maxItems (W64 2)) e (by word)
      (by rw [hdiv]; exact He_lookup) Hccs $$ [$Hcow $Hc'] as %n2 ⟨H1, H2⟩
    rw [hdiv]
    unfold nodeShallow nodeFields
    icases Hsh with ⟨%isl, %csl, ⟨%Hnn, Hfi, Hfc, Hfw⟩, Hisl, Hicap, Hcsl, Hccap⟩
    wp_apply wp_insertAt _ isl _ i e.1 Hi (by rw [List.length_map]; word) $$ [$Hfi $Hisl $Hicap]
      as %isl' ⟨Hfi, Hisl, Hicap⟩
    wp_apply wp_insertAt _ csl _ (i + W64 1) n2 (by word) (by rw [List.length_set]; word) $$ [$Hfc $Hcsl $Hccap]
      as %csl' ⟨Hfc, Hcsl, Hccap⟩
    iapply HΦ
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    isplitr
    · ipureintro; rfl
    iexists e
    isplitr
    · ipureintro; exact He_lookup
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
    iexists _
    isplitl [Hfi Hfc Hfw Hisl Hicap Hcsl Hccap]
    · iexists isl', csl'
      rw [List.map_append, List.map_cons, List.map_take, List.map_drop]
      iframe
      ipureintro; exact Hnn
    · iapply ownNodes_split_child o c f less _ ps cs (sint.nat i) hb Hpl c' n2
      iframe Hch
      isplitl [H1]
      · iapply ownNode_of_owned; iexact H1
      · iapply ownNode_of_owned; iexact H2

end proof

end Btree
end EtcdGrove
end Perennial
