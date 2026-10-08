import EtcdGrove.Btree.Spec.items__insertAt
import EtcdGrove.Btree.ListLemmas

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

theorem items.insertAt.wp_proof : items.insertAt.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ s sl vs index item Hi0 Hi1
  wp_start as ⟨Hs, Hsl, Hcap⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_apply wp_slice_literal (l := [zero_val V])
  isplitr
  · ipureintro; rfl
  iintro %zsl ⟨Hz, Hzcap⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hz] as %sl1 ⟨Hsl, Hcap, _⟩
  ihave %Hlen1 := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_append, List.length_singleton] at Hlen1
  ihave %Hwf1 := ownSlice_wf _ _ _ $$ Hsl
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
    wp_auto
    wp_apply (wp_slice_copy_within (st := items.ty T) sl1 _ (index + W64 1) sl1.len index sl1.len
      ⟨by word, by word, by word⟩ ⟨by word, by word, by word⟩) $$ [$Hsl] as %n ⟨_, Hsl⟩
    have hi1 : sint.nat (index + W64 1) = sint.nat index + 1 := by word
    have hn : sint.nat sl1.len = vs.length + 1 := by omega
    rw [hi1, hn, shiftRight_list vs (zero_val V) (sint.nat index) (by word)]
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_store_slice_index sl1 (sint.Z index) _ item $$ [$Hsl] as Hsl
    · ipureintro; constructor
      · word
      · simp only [List.length_append, List.length_take, List.length_drop,
          List.length_singleton]; word
    rw [show (sint.Z index).toNat = sint.nat index from rfl,
      insertAt_list vs (zero_val V) item (sint.nat index) (by word)]
    iapply HΦ
    iframe
  · exfalso; word

end proof

end Btree
end EtcdGrove
end Perennial
