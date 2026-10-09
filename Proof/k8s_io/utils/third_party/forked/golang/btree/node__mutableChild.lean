module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__mutableChild
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__mutableFor
public import Proof.k8s_io.utils.third_party.forked.golang.btree.NodeLemmas

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

theorem node.mutableChild.wp_proof
    (wp_mutableFor : node.mutableFor.spec (GF := GF) (hG := hG)) :
    node.mutableChild.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less n is ps i p t Hi Hp
  wp_start as ⟨#Hcow, Hsh, Hc⟩
  unfold nodeShallow nodeFields
  icases Hsh with ⟨%isl, %csl, ⟨%Hnn, Hfi, Hfc, Hfw⟩, Hisl, Hicap, Hcsl, Hccap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hcsl
  have hb : sint.nat i < ps.length := by
    rcases List.getElem?_eq_some_iff.1 Hp with ⟨h, _⟩; exact h
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi, by word⟩)]
  wp_apply wp_load_slice_index csl (sint.Z i) ps _ p Hi $$ [Hcsl] as Hcsl
  · iframe; ipureintro; exact Hp
  wp_apply wp_mutableFor o c f less p t $$ [$Hcow $Hc] as %c' Hc'
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi, by word⟩)]
  wp_apply wp_store_slice_index csl (sint.Z i) ps c' $$ [Hcsl] as Hcsl
  · iframe; ipureintro; exact ⟨Hi, by word⟩
  iapply HΦ
  iframe Hc'
  iexists isl, csl
  iframe
  ipureintro; exact Hnn

end proof

end btree
end EtcdGrove
end Perennial
