/-
`fieldpath.SetNodeMap.Iterate`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Iterate
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

theorem fieldpath.SetNodeMap.Iterate.wp_proof :
    fieldpath.SetNodeMap.Iterate.spec (GF := GF) := fun l D f I => by
  wp_start as ⟨#Hl, HI, #Hf⟩
  unfold isNodes isNodesV
  icases Hl with ⟨%m, #Hm, %ns, %cs, #Hns, #Hcs, %hc⟩
  ihave %hlen := fpD.trieRepC_length ns cs $$ Hcs
  ihave %hwf := fpD.trieRepC_wf ns cs $$ Hcs
  ihave %hsl := ownSlice_len $$ Hns
  have hnd := fpD.sorted_nodup _ hwf hc.1
  iStructNamed Hm
  wp_auto
  ihave HL : iprop(∃ k : w64, "i" ∷ i_ptr ↦ k ∗ "n" ∷ (∃ nv : fieldpath.setNode, n_ptr ↦ nv) ∗
      "HI" ∷ I ((cs.map Prod.fst).take (sint.nat k)) ∗
      "%hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z m.members'.len⌝) $$ [i n HI]
  · iexists W64 0; iframe; isplitl [n]
    · iexists _; iexact n
    · ipureintro; word
  wp_for HL
  wp_if_destruct
  · rw [if_pos ⟨hk.1, Hif⟩]
    have hkn : sint.nat k < ns.length := by word
    obtain ⟨n0, hn0⟩ : ∃ n0, ns[sint.nat k]? = some n0 := ⟨_, List.getElem?_eq_getElem hkn⟩
    icases n with ⟨%nv, n⟩
    wp_apply (wp_load_slice_index m.members' (sint.Z k) ns DFrac.discard n0 hk.1) $$ [$Hns] as _
    · ipureintro; exact hn0
    ihave ⟨%c, %hc', #He, -⟩ := fpD.trieRepC_lookup ns cs (sint.nat k) n0 hn0 $$ Hcs
    have hx : c.1 ∈ D.heads := (fpD.heads_iff cs D hc.2.1 hc.2.2 c.1).2
      (List.mem_map.2 ⟨c, List.mem_of_getElem? hc', rfl⟩)
    have hkx : (cs.map Prod.fst)[sint.nat k]? = some c.1 := by simp [hc']
    have hx' := fpD.not_mem_take_of_nodup hnd hkx
    ihave #Hfx := Hf $$ %((cs.map Prod.fst).take (sint.nat k)) %n0.pathElement' %c.1 %(And.intro hx hx')
    wp_apply Hfx $$ [$HI $He] as HI
    wp_for_post
    iframe
    iexists k + W64 1
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, fpD.take_succ_of hkx]
    iframe
    isplitl [n]
    · iexists _; iexact n
    · ipureintro; word
  · have hkl : sint.nat k = (cs.map Prod.fst).length := by simp; word
    rw [hkl, List.take_length]
    iapply HΦ
    iexists _; iframe HI
    ipureintro
    refine ⟨hnd, FSet.ext' (fun x => ?_)⟩
    rw [FSet.mem_ofList', fpD.heads_iff cs D hc.2.1 hc.2.2]

end proof

end smd
end EtcdGrove
end Perennial
