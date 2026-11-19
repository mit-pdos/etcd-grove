/-
`fieldpath.SetNodeMap.iteratePrefix`: a member of the recursion cluster `fieldpath.iteratePrefixRec` (`iteratePrefixRec.lean`); its proof is the
projection of the cluster's (its body is `SetNodeMap__iteratePrefixBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__iteratePrefixBody
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsIter
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

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

theorem fieldpath.SetNodeMap.iteratePrefix.wp_proofBody :
    fieldpath.SetNodeMap.iteratePrefix.specBody (GF := GF) := by
  unfold fieldpath.SetNodeMap.iteratePrefix.specBody fieldpath.iteratePrefixRec.specI
    fieldpath.Set.iteratePrefix.specI fieldpath.SetNodeMap.iteratePrefix.specI
  iintro #IH
  iintro %l %D %ps %es %pre %f %T %I %done0
  wp_start as ⟨#Hn, Hps, Hcap, #Hes, HI, %hpre, #Hf⟩
  unfold isNodes isNodesV
  icases Hn with ⟨%m, #Hm, %ns, %cs, #Hns, #Hcs, %hc⟩
  ihave %hlen := fpD.trieRepC_length ns cs $$ Hcs
  ihave %hwf := fpD.trieRepC_wf ns cs $$ Hcs
  ihave %hsl := ownSlice_len $$ Hns
  ihave %hesl := isPEs_length_law_holds es pre $$ Hes
  have hnd := fpD.sorted_nodup _ hwf hc.1
  iStructNamed Hm
  wp_auto
  ihave HL : iprop(∃ k : w64, "i" ∷ i_ptr ↦ k ∗ "n" ∷ (∃ nv : fieldpath.setNode, n_ptr ↦ nv) ∗
      "Hps" ∷ ps ↦* es ∗ "Hcap" ∷ ownSliceCap fieldpath.PathElement ps (DFrac.own 1) ∗
      "HI" ∷ (∃ dsk : List Path, ⌜fpD.DoneK pre D (cs.map Prod.fst) (sint.nat k) dsk⌝ ∗
        I (done0 ++ dsk)) ∗
      "%hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z m.members'.len⌝) $$ [i n Hps Hcap HI]
  · iexists W64 0; iframe; isplitl [n]
    · iexists _; iexact n
    isplitl [HI]
    · iexists []; simp only [List.append_nil]; iframe
      ipureintro; rw [show sint.nat (W64 0) = 0 by rfl]; exact fpD.doneK_zero _ _ _
    · ipureintro; word
  irename «prefix» => Hpcell
  wp_for HL
  wp_if_destruct
  · have Hif' : sint.Z k < sint.Z m.members'.len := by simpa [intoVal_eq_iff] using Hif
    rw [if_pos ⟨hk.1, Hif'⟩]
    have hkn : sint.nat k < ns.length := by word
    obtain ⟨n0, hn0⟩ : ∃ n0, ns[sint.nat k]? = some n0 := ⟨_, List.getElem?_eq_getElem hkn⟩
    icases n with ⟨%nv, n⟩
    wp_apply (wp_load_slice_index m.members' (sint.Z k) ns DFrac.discard n0 hk.1) $$ [$Hns] as _
    · ipureintro; exact hn0
    ihave ⟨%c, %hc', #He, #Ht⟩ := fpD.trieRepC_lookup ns cs (sint.nat k) n0 hn0 $$ Hcs
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply (wp_slice_append_undo ps es _ [n0.pathElement'] (DFrac.own 1)) $$ [$Hps $Hcap $Hsl]
      as %ps' ⟨Hps', Hcap', -, Hback⟩
    rcases c with ⟨e, t⟩
    have hm : (e, t) ∈ cs := List.mem_of_getElem? hc'
    have hkx : (cs.map Prod.fst)[sint.nat k]? = some e := by simp [hc']
    obtain ⟨hct, -⟩ := fpD.canonicalC_mem cs hc.2.1 e t hm
    ihave #HS : iprop(isSet n0.set' (D.under e)) $$ []
    · unfold isSet; iexists t; iframe Ht; ipureintro
      exact ⟨hct, fun r => fpD.under_iff cs D hnd hc.2.2 e t hm r⟩
    ihave #Hes' : iprop(isPEs (es ++ [n0.pathElement']) (pre ++ [e])) $$ []
    · iapply (isPEs_app_law_holds es [n0.pathElement'] pre [e] hesl).2
      iframe Hes
      iapply (isPEs_cons_law_holds n0.pathElement' [] e []).2
      iframe He
      unfold isPEs; rw [fpL.isPEL_nil_eq]; itrivial
    icases HI with ⟨%dsk, %hdsk, HI⟩
    icases IH with ⟨#HSp, -⟩
    wp_apply HSp $$ %n0.set' %(D.under e) %ps' %(es ++ [n0.pathElement']) %(pre ++ [e]) %f %T %I
      %(done0 ++ dsk) [Hps' Hcap' HI] as ⟨Hps', Hcap', %dsc, %hdsc, HI⟩
    · iframe
      isplit; · iexact HS
      isplit; · iexact Hes'
      isplit
      · ipureintro
        intro q hq
        have hq' := (PathSet_mem_under_law_holds D e q).1 hq
        rw [List.append_assoc, List.singleton_append]
        refine ⟨(hpre _ hq'.2).1, ?_⟩
        rw [List.mem_append, not_or]
        exact ⟨(hpre _ hq'.2).2, fpD.doneK_not_mem hdsk hnd hkx q⟩
      · iexact Hf
    ihave ⟨Hps, Hcap⟩ := Hback $$ [Hps' Hcap']
    · iframe
    wp_for_post
    iframe
    iexists k + W64 1
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
    iframe
    isplitl [n]
    · iexists _; iexact n
    isplitl [HI]
    · iexists (dsk ++ dsc)
      isplitr
      · ipureintro
        refine fpD.doneK_step hnd hkx (fun q hq => ?_) hdsk hdsc
        obtain ⟨e', t', r, -, h1, h2, -⟩ := fpD.nodes_mem cs D hc.2.2 q hq
        exact ⟨e', r, h1, h2⟩
      · rw [← List.append_assoc]; iexact HI
    · ipureintro; word
  · icases HI with ⟨%dsk, %hdsk, HI⟩
    have hkl : sint.nat k = (cs.map Prod.fst).length := by simp; word
    rw [hkl] at hdsk
    iapply HΦ
    iframe Hps Hcap
    iexists dsk
    isplitr
    · ipureintro
      refine fpD.doneK_all (fun q hq => ?_) hdsk
      obtain ⟨e', t', r, hm, h1, -, -⟩ := fpD.nodes_mem cs D hc.2.2 q hq
      exact ⟨e', List.mem_map.2 ⟨_, hm, rfl⟩, by simp [h1]⟩
    · iexact HI

end proof

end smd
end EtcdGrove
end Perennial
