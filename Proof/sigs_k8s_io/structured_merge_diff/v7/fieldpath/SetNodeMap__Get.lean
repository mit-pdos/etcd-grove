/-
`fieldpath.SetNodeMap.Get`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Compare
public import Spec.slices.BinarySearchFunc
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsGet

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

theorem fieldpath.SetNodeMap.Get.wp_proof
    (h_PathElement_Compare : fieldpath.PathElement.Compare.spec (GF := GF))
    (h_slices_BinarySearchFunc : EtcdGrove.slices.BinarySearchFunc.spec (GF := GF)) :
    fieldpath.SetNodeMap.Get.spec (GF := GF) := fun l D e pe => by
  wp_start as ⟨#Hn, #He⟩
  unfold isNodes
  icases Hn with ⟨%m, #Hl, Hm⟩
  icases (fpC.isNodesV_view m D).1 $$ Hm with ⟨%ns, %nl, #Hns, #Hnl, %hok⟩
  ihave %hmd := fpG.nodesL_mdl ns nl pe $$ Hnl
  ihave %hlen := fpC.nodesL_length ns nl $$ Hnl
  ihave %hp := fpL.isPE_wf' e pe $$ He
  ihave %hsl := ownSlice_len $$ Hns
  have hw := fpC.nlok_wf hok.1
  iStructNamed Hl
  wp_auto
  wp_apply (h_slices_BinarySearchFunc (E := fieldpath.setNode) fieldpath.PathElement.ty m.members' ns
    DFrac.discard e _ (fun a => PE.compare (fpA.mdl ns (fpC.keys nl) pe a) pe) iprop(True))
    $$ [$Hns] as %i %found ⟨-, -, %hi1, %hi2, %hi3⟩
  · isplitr
    · itrivial
    isplit
    · imodintro
      iintro %a %ha
      imodintro
      iintro %Φ' - HΦ'
      have hk := fpA.peIdx_get ns a ha
      ihave ⟨%x, %S, %hx, #Ha, -⟩ := fpC.nodesL_lookup ns nl _ a hk $$ Hnl
      have hx' : x = fpA.mdl ns (fpC.keys nl) pe a := by
        have := hmd _ a hk; simp only [fpC.keys, List.getElem?_map, hx] at this
        exact Option.some.inj this
      subst hx'
      wp_auto
      wp_method_call; wp_call; wp_auto
      wp_apply (h_PathElement_Compare a.pathElement' e (fpA.mdl ns (fpC.keys nl) pe a) pe) $$ [$Ha $He] as %r %hr
      iapply HΦ'
      iframe
      ipureintro; exact ⟨trivial, hr⟩
    · ipureintro
      intro k j ek ej hk hj hkj
      exact fpA.sorted_signum hw hp hok.1.1 k j _ _ (hmd k ek hk) (hmd j ej hj) hkj
  have hlen' : ns.length = (fpC.keys nl).length := by simp [fpC.keys, hlen]
  obtain ⟨hbs, hf⟩ := fpA.bs_transfer ns (fpC.keys nl) pe (fpA.mdl ns (fpC.keys nl) pe) hmd hlen' _
    found hi1 hi2 hi3
  have hfound := hf.trans (fpA.bs_found hw hp hok.1.1 hbs)
  have hheads := fpG.heads_iff hok.1 D hok.2 pe
  cases found
  · wp_auto
    iapply HΦ
    isplit
    · ipureintro; rw [hheads, ← hfound]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; trivial
  · obtain ⟨x, hx, hc⟩ := hf.1 rfl
    have hil : (sint.Z i).toNat < ns.length := by
      rw [hlen']; exact (List.getElem?_eq_some_iff.1 hx).1
    have hxw : x.wf = true := hw x (List.mem_of_getElem? hx)
    have hxe : x = pe := (PE_compare_eq_zero_law_holds x pe hxw hp).1 hc
    subst hxe
    obtain ⟨n, hn⟩ : ∃ n, ns[(sint.Z i).toNat]? = some n := ⟨_, List.getElem?_eq_getElem hil⟩
    icases fpC.node_at m.members' ns nl (sint.Z i) n hi1.1 hn $$ [$Hns $Hnl] with
      ⟨%pe', %S, %h1, #Hpef, #Hsf, #Hpe', #HS⟩
    have hpe' : pe' = x := by
      have := hx; simp only [fpC.keys, List.getElem?_map, h1] at this
      exact Option.some.inj this
    subst hpe'
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z m.members'.len := by
      refine ⟨hi1.1, ?_⟩
      have h3 : (sint.Z i).toNat < sint.nat m.members'.len := hsl.1 ▸ hil
      simp only [sint.nat] at h3
      have key : ∀ a b : Int, a.toNat < b.toNat → a < b := by intro a b h; omega
      exact key _ _ h3
    have hnl : (pe', S) ∈ nl := List.mem_of_getElem? h1
    wp_auto
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_auto
    iapply HΦ
    isplit
    · ipureintro; rw [hheads, ← hfound]
    · simp only [↓reduceIte]
      rw [fpG.under_eq hok.1 D hok.2 hnl]
      iexact HS

end proof

end smd
end EtcdGrove
end Perennial
