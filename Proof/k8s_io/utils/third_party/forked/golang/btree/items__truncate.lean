module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.items__truncate
public import Proof.k8s_io.utils.third_party.forked.golang.btree.ListLemmas

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

theorem items.truncate.wp_proof : items.truncate.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ s sl vs index Hi0 Hi1
  wp_start as ⟨Hs, Hsl, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word, by word⟩)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
  wp_auto
  icases (ownSlice_split_all index sl _ _ ⟨by word, by word⟩).1 $$ Hsl with ⟨Hsl1, Hsl2⟩
  ihave HI : (∃ (i : w64) (ws : List V),
      "i" ∷ i_ptr ↦ i ∗
      "Hc" ∷ slice.slice sl V index sl.len ↦* ws ∗
      "%Hi" ∷ ⌜ws.length = sint.nat sl.len - sint.nat index ∧ 0 ≤ sint.Z i⌝ : IProp GF)
    $$ [i Hsl2]
  · iexists (W64 0), _
    iframe
    ipureintro; constructor
    · simp only [List.length_drop]; word
    · decide
  wp_for HI
  ihave %Hlc := ownSlice_len _ _ _ $$ Hc
  simp only [slice.slice] at Hlc
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.2, by word⟩)]
    wp_apply wp_store_slice_index _ (sint.Z i) ws (zero_val V) $$ [Hc] as Hc
    · iframe; ipureintro; constructor
      · exact Hi.2
      · word
    wp_for_post
    iframe
    iexists (i + W64 1), _
    iframe
    ipureintro; constructor
    · simp only [List.length_set]; exact Hi.1
    · word
  · ihave Hcap := ownSlice_slice_absorb_capacity sl _ (W64 0) index
      ⟨by decide, by word, by word⟩ $$ [Hc Hcap]
    · iframe
    iapply HΦ
    iframe

end proof

end btree
end EtcdGrove
end Perennial
