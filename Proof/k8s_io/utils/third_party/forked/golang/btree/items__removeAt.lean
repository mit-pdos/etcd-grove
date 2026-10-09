module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.items__removeAt
public import Proof.k8s_io.utils.third_party.forked.golang.btree.ListLemmas
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Lemmas.Low

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

theorem items.removeAt.wp_proof : items.removeAt.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ s sl vs index v Hi0 Hv
  wp_start as ⟨Hs, Hsl, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
  have hi : sint.nat index < vs.length := by
    rcases List.getElem?_eq_some_iff.mp Hv with ⟨h, _⟩; exact h
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi0, by word⟩)]
  wp_apply wp_load_slice_index sl (sint.Z index) vs _ v Hi0 $$ [Hsl] as Hsl
  · iframe; ipureintro; exact Hv
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
  wp_auto
  wp_apply (wp_slice_copy_within (st := items.ty T) sl vs index sl.len (index + W64 1) sl.len
    ⟨by word, by word, by word⟩ ⟨by word, by word, by word⟩) $$ [$Hsl] as %n ⟨_, Hsl⟩
  have hl : sint.nat sl.len = vs.length := Hlen.1.symm
  have hi1 : sint.nat (index + W64 1) = sint.nat index + 1 := by word
  have hl1 : (sint.Z (sl.len - W64 1)).toNat = vs.length - 1 := by word
  have hl1' : sint.nat (sl.len - W64 1) = vs.length - 1 := by word
  rw [hl, hi1]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  wp_apply wp_store_slice_index sl (sint.Z (sl.len - W64 1)) _ (zero_val V) $$ [Hsl] as Hsl
  · iframe; ipureintro; constructor
    · word
    · simp only [List.length_append, List.length_take, List.length_drop, subslice]; word
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
  wp_auto
  icases (ownSlice_split_all (sl.len - W64 1) sl _ _ ⟨by word, by word⟩).1 $$ Hsl with ⟨Hsl1, Hsl2⟩
  ihave Hcap := ownSlice_slice_absorb_capacity sl _ (W64 0) (sl.len - W64 1)
    ⟨by decide, by word, by word⟩ $$ [Hsl2 Hcap]
  · iframe
  rw [hl1, hl1', removeAt_list vs (sint.nat index) (zero_val V) hi]
  iapply HΦ
  iframe

end proof

end btree
end EtcdGrove
end Perennial
