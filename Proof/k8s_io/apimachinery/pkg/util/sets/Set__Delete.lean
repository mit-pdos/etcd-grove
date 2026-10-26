/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/sets/Set__Delete.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Delete
public import Proof.k8s_io.apimachinery.pkg.util.sets.DeleteNamed

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

theorem Set.Delete.wp_proof [EtcdGrove.DeleteNamedMapSemantics] : Set.Delete.spec (GF := GF) (hG := hG) := by
  intro K _ _ _ _ T _ _ m s sl dq ks
  wp_start as ⟨Hm, Hsl⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n : w64) (x : K),
      "i" ∷ i_ptr ↦ n ∗
      "item" ∷ item_ptr ↦ x ∗
      "Hm" ∷ m ↦$ deleteAll s (ks.take (sint.nat n)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ks.length⌝) $$ [i item Hm]
  · iexists W64 0, _
    iframe
    ipureintro
    exact ⟨by decide, by simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ks.length := by word
    obtain ⟨e, He⟩ : ∃ e, ks[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) ks dq e Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact He
    wp_apply wp_mapDelete_named (key_type := T) (elem_type := Empty.ty) $$ Hm as Hm
    wp_for_post
    iframe
    iexists n + W64 1, e
    iframe
    have Htake : ks.take (sint.nat (n + W64 1)) = ks.take (sint.nat n) ++ [e] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
      rw [List.take_succ, He]; rfl
    rw [Htake, deleteAll_append]
    iframe
    ipureintro
    constructor <;> word
  · rw [show sint.nat n = ks.length by word, List.take_length]
    iapply HΦ
    iframe

end proof

end sets
end EtcdGrove
end Perennial
