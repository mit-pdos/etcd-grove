/-
`fieldpath.NewSet`: proved over its callees' specs (the hypotheses): a loop inserting the paths
one by one, the set being the first `k` paths' (`fpN.ofList_take_succ`), at most `k` of them.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsSet
import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Sets

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.NewSet.wp_proof
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF)) :
    fieldpath.NewSet.spec (GF := GF) := fun s dq dq' ss ps => by
  wp_start as ⟨Hs, Hps⟩
  ihave %hlen := ownSlice_len $$ Hs
  ihave %hlp := fpN.isPathsF_length dq' ss ps $$ Hps
  wp_auto
  ihave Hr := (ownSet_empty_law_holds _) $$ «$r0»
  ihave HL : iprop(∃ (k : w64), "i" ∷ i_ptr ↦ k ∗ "p" ∷ (∃ pv : GoSlice, p_ptr ↦ pv) ∗
      "Hr" ∷ ownSet «$r0_ptr» (PathSet.ofList (ps.take (sint.nat k))) ∗
      "%hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.len⌝) $$ [i p Hr]
  · iexists W64 0; iframe; isplitl [p]
    · iexists _; iexact p
    ipureintro; word
  wp_for HL
  wp_if_destruct
  · rw [if_pos ⟨hk.1, Hif⟩]
    have hkn : sint.nat k < ss.length := by word
    list_elem ss (sint.nat k) as s0
    list_elem ps (sint.nat k) as p0
    wp_apply (wp_load_slice_index s (sint.Z k) ss dq s0 hk.1) $$ [$Hs] as Hs
    · ipureintro; exact Hs0_lookup
    icases p with ⟨%pv, p⟩
    wp_auto
    icases fpN.isPathsF_acc dq' ss ps (sint.nat k) s0 p0 Hs0_lookup Hp0_lookup $$ Hps with ⟨Hp0, Hback⟩
    have hcard := fpN.card_ofList_le (ps.take (sint.nat k))
    wp_apply h_Set_Insert $$ [$Hr $Hp0] as ⟨Hr, Hp0⟩
    · iframe #; ipureintro
      show FSet.card _ < _
      simp only [List.length_take] at hcard
      word
    ihave Hps := Hback $$ Hp0
    wp_for_post
    iframe
    iexists k + W64 1
    iframe
    isplitl [p]
    · iexists _; iexact p
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, ← fpN.ofList_take_succ ps _ p0 Hp0_lookup]
    iframe
    ipureintro; word
  · have hkl : sint.nat k = ps.length := by word
    rw [hkl, List.take_length]
    iapply HΦ
    iframe

end proof

end smd
end EtcdGrove
end Perennial
