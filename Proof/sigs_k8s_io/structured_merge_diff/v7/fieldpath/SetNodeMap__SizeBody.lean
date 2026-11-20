/-
`fieldpath.SetNodeMap.Size`: a member of the recursion cluster `fieldpath.SizeRec` (`SizeRec.lean`); its proof is the
projection of the cluster's (its body is `SetNodeMap__SizeBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__SizeBody
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsCard

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

theorem fieldpath.SetNodeMap.Size.wp_proofBody :
    fieldpath.SetNodeMap.Size.specBody (GF := GF) := by
  unfold fieldpath.SetNodeMap.Size.specBody fieldpath.SizeRec.specI
    fieldpath.Set.Size.specI fieldpath.SetNodeMap.Size.specI
  iintro #IH
  iintro %l %D
  wp_start as #Hn
  unfold isNodes
  icases Hn with ⟨%m, #Hm, Hv⟩
  icases (fpC.isNodesV_view m D).1 $$ Hv with ⟨%ns, %nl, #Hns, #Hl, %hok⟩
  have hD : D = fpC.nlPaths nl := FSet.ext' hok.2
  subst hD
  have hnd : (fpC.keys nl).Nodup := fpC.sorted_nodup _ (fpC.nlok_wf hok.1) hok.1.1
  ihave %hlen := fpC.nodesL_length ns nl $$ Hl
  ihave %hsl := ownSlice_len $$ Hns
  iStructNamed Hm
  wp_auto
  ihave HL : iprop(∃ (k c : w64), "i" ∷ i_ptr ↦ k ∗ "count" ∷ count_ptr ↦ c ∗
      "v" ∷ (∃ nv : fieldpath.setNode, v_ptr ↦ nv) ∗
      "%hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z m.members'.len ∧
        ((fpC.nlPaths nl).card < 2 ^ 63 →
          sint.Z c = ((fpC.nlPaths (nl.take (sint.nat k))).card : Int))⌝) $$ [i count v]
  · iexists W64 0, W64 0; iframe; isplitl [v]
    · iexists _; iexact v
    ipureintro
    refine ⟨by word, by word, fun _ => ?_⟩
    rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero]
    show (0 : Int) = ((FSet.empty : PathSet).card : Int)
    rfl
  wp_for HL
  wp_if_destruct
  · have Hif' : sint.Z k < sint.Z m.members'.len := by simpa [intoVal_eq_iff] using Hif
    rw [if_pos ⟨hk.1, Hif'⟩]
    have hkn : sint.nat k < ns.length := by word
    list_elem ns (sint.nat k) as n0
    icases v with ⟨%nv, v⟩
    wp_apply (wp_load_slice_index m.members' (sint.Z k) ns DFrac.discard n0 hk.1) $$ [$Hns] as _
    · ipureintro; exact Hn0_lookup
    icases fpC.node_at m.members' ns nl (sint.Z k) n0 hk.1 Hn0_lookup $$ [$Hns $Hl] with
      ⟨%pe, %S, %h1, #Hpe1f, #Hs1f, #Hpe, #HS⟩
    icases IH with ⟨#HSz, -⟩
    wp_apply HSz $$ %n0.set' %S [] as %r %hr
    · iframe #
    wp_for_post
    iframe
    iexists k + W64 1, c + r
    iframe
    isplitl [v]
    · iexists _; iexact v
    ipureintro
    have hkl : sint.nat k < nl.length := by omega
    have hnlk : nl[sint.nat k] = (pe, S) := by
      have := h1; simp only [sint.nat] at hkl ⊢; rw [List.getElem?_eq_getElem hkl] at this
      exact Option.some.inj this
    refine ⟨by word, by word, fun hlt => ?_⟩
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, fpK.nl_card_take nl _ hkl hnd, hnlk]
    have hle := fpK.nl_card_take_le nl (sint.nat k + 1)
    rw [fpK.nl_card_take nl _ hkl hnd, hnlk] at hle
    have hc := hk.2.2 hlt
    simp only at hle ⊢
    have hrS := hr S.card ((FSet.hasCard_iff _ _).2 rfl) (by omega)
    push_cast
    word
  · iapply HΦ
    ipureintro
    intro n hn hlt
    obtain rfl := (FSet.hasCard_iff _ _).1 hn
    rw [hk.2.2 hlt]
    have hkl : sint.nat k = nl.length := by
      have : ¬ sint.Z k < sint.Z m.members'.len := by simpa [intoVal_eq_iff] using Hif
      word
    rw [hkl, List.take_length]

end proof

end smd
end EtcdGrove
end Perennial
