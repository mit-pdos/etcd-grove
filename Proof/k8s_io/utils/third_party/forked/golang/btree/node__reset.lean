module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__reset
public import Spec.k8s_io.utils.third_party.forked.golang.btree.copyOnWriteContext__freeNode
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Lemmas.Alloc

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

theorem node.reset.wp_proof
    (wp_cow_freeNode : copyOnWriteContext.freeNode.spec (GF := GF) (hG := hG)) :
    node.reset.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less n t
  iloeb as IH generalizing %n %t
  wp_start as ⟨#Hcow, Hn⟩
  cases t with
  | node is cs =>
  ihave Hst : (∃ (dq : DFrac) (csl : GoSlice) (ps : List Loc),
      "Hch" ∷ structFieldRef (node V) go!"children" n ↦{dq} csl ∗
      "Hcsl" ∷ csl ↦*{dq} ps ∗
      "Hkids" ∷ ownNodes o c f less (DFrac.own 1) ps cs ∗
      "Hback" ∷ (structFieldRef (node V) go!"children" n ↦{dq} csl -∗ csl ↦*{dq} ps -∗
        ((∃ (is : List (V × K)) (ps : List Loc), nodeShallow (V := V) c (DFrac.own 1) n is ps) ∨
         ∃ t : Tree (V × K), frozen o c f less n t)) : IProp GF) $$ [Hn]
  · rw [ownNode_node]
    icases Hn with (Hown | #Hfr)
    · unfold ownedNode nodeShallow nodeFields
      icases Hown with ⟨%ps, ⟨%isl, %csl, ⟨%Hnn, Hi, Hch, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩, Hkids⟩
      iexists DFrac.own 1, csl, ps
      iframe
      iintro Hch Hcsl
      ileft; iexists _, ps, isl, csl
      iframe
      ipureintro; exact Hnn
    · icases frozen_children o c f less n is cs $$ Hfr with ⟨%csl, %ps, #Hch, #Hcsl, #Hfl⟩
      iexists DFrac.discard, csl, ps
      unfold named
      isplitr; · iexact Hch
      isplitr; · iexact Hcsl
      isplitr
      · iapply frozenList_ownNodes; iexact Hfl
      iintro - -
      iright; iexists _; iexact Hfr
  iNamed Hst
  ihave %Hlen := ownNodes_length _ _ _ _ _ _ _ $$ Hkids
  ihave %Hslen := ownSlice_len _ _ _ $$ Hcsl
  wp_auto
  ihave HI : (∃ (i : w64) (k : Loc),
      "i" ∷ i_ptr ↦ i ∗
      "child" ∷ child_ptr ↦ k ∗
      "Hkids" ∷ ownNodes o c f less (DFrac.own 1) (ps.drop (sint.nat i)) (cs.drop (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z csl.len⌝ : IProp GF) $$ [i child Hkids]
  · iexists W64 0, _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · list_elem ps (sint.nat i) as p
    list_elem cs (sint.nat i) as tc
    rw [drop_eq_cons_of_getElem? ps _ p Hp_lookup, drop_eq_cons_of_getElem? cs _ tc Htc_lookup,
      ownNodes_cons]
    icases Hkids with ⟨Hp, Hkids⟩
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z csl.len := ⟨Hi.1, Hif⟩
    simp only [Hb, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index csl (sint.Z i) ps dq p Hi.1 $$ [Hcsl] as Hcsl
    · iframe; ipureintro; exact Hp_lookup
    wp_apply IH $$ %p %tc [Hp] as %b _
    · iframe Hp; iexact Hcow
    cases b <;> wp_auto
    · wp_for_post
      iapply HΦ; itrivial
    · wp_for_post
      iframe
      iexists i + W64 1, p
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      iframe
      ipureintro; constructor <;> word
  · wp_apply (wp_cow_freeNode (V := V) (T := T) o c f less n) $$ [Hback Hch Hcsl] as %r _
    · iframe Hcow
      iapply Hback $$ Hch Hcsl
    wp_end

end proof

end btree
end EtcdGrove
end Perennial
