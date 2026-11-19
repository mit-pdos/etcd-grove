/-
`fieldpath.PathElementMap.Get`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Compare
public import Spec.slices.BinarySearchFunc
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsPESet

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

theorem fieldpath.PathElementMap.Get.wp_proof
    (h_PathElement_Compare : fieldpath.PathElement.Compare.spec (GF := GF))
    (h_slices_BinarySearchFunc : EtcdGrove.slices.BinarySearchFunc.spec (GF := GF)) :
    fieldpath.PathElementMap.Get.spec (GF := GF) := fun l M e pe => by
  wp_start as ⟨Hs, #He⟩
  unfold ownPEMap ownPEMapV
  icases Hs with ⟨%v, Hl, %ns, %xs, Hm, Hcap, #Hx, %h⟩
  icases fpA.pemap_members_upd l v (DFrac.own 1) $$ Hl with ⟨Hf, Hback⟩
  ihave %hmd0 := fpA.isPEL_mdl (ns.map (·.PathElement')) (xs.map (·.1)) pe $$ Hx
  ihave %hw := fpL.isPEL_wf _ _ $$ Hx
  ihave %hlen := fpL.isPEL_length _ _ $$ Hx
  ihave %hp := fpL.isPE_wf' e pe $$ He
  have hmd : ∀ (k : Nat) (a : fieldpath.pathElementValue), ns[k]? = some a →
      (xs.map (·.1))[k]? = some (fpA.mdl (ns.map (·.PathElement')) (xs.map (·.1)) pe a.PathElement') := by
    intro k a hk; exact hmd0 k a.PathElement' (by simp [hk])
  wp_auto
  wp_apply (h_slices_BinarySearchFunc (E := fieldpath.pathElementValue) fieldpath.PathElement.ty v.members' ns (DFrac.own 1) e _
    (fun a => PE.compare (fpA.mdl (ns.map (·.PathElement')) (xs.map (·.1)) pe a.PathElement') pe) iprop(True)) $$ [$Hm] as %i %found ⟨Hm, -, %hi1, %hi2, %hi3⟩
  · isplitr
    · itrivial
    isplit
    · imodintro
      iintro %a %ha
      imodintro
      iintro %Φ' - HΦ'
      have hk := fpA.peIdx_get ns a ha
      ihave ⟨%x, %hx, Ha⟩ := fpL.isPEL_lookup _ _ (fpA.peIdx ns a) a.PathElement' (by simp [hk]) $$ Hx
      have hx' : x = fpA.mdl (ns.map (·.PathElement')) (xs.map (·.1)) pe a.PathElement' := by
        have := hmd _ a hk; rw [hx] at this; exact Option.some.inj this
      subst hx'
      wp_auto
      wp_method_call; wp_call; wp_auto
      wp_apply (h_PathElement_Compare a.PathElement' e _ pe) $$ [$Ha $He] as %r %hr
      iapply HΦ'
      iframe
      ipureintro; exact ⟨trivial, hr⟩
    · ipureintro
      intro k j ek ej hk hj hkj
      exact fpA.sorted_signum hw hp h.2.1 k j _ _ (hmd k ek hk) (hmd j ej hj) hkj
  have hlen' : ns.length = (xs.map (·.1)).length := by simpa using hlen
  obtain ⟨hbs, hf⟩ := fpA.bs_transfer ns (xs.map (·.1)) pe _ hmd hlen' _ found hi1 hi2 hi3
  have hnd := fpA.sorted_nodup _ hw h.2.1
  have hM : ∀ k, M k = fpA.kvFind xs k := h.2.2
  cases found
  case true =>
    obtain ⟨k, hk, hc⟩ := hf.1 rfl
    have hkw := hw k (List.mem_of_getElem? hk)
    have hke := (PE_compare_eq_zero_law_holds k pe hkw hp).1 hc
    subst hke
    have hi' : (sint.Z i).toNat < ns.length := by
      rw [hlen']; exact (List.getElem?_eq_some_iff.1 hk).1
    have hnv : ns[(sint.Z i).toNat]? = some ns[(sint.Z i).toNat] := List.getElem?_eq_getElem hi'
    ihave %hsl := ownSlice_len $$ Hm
    have hb1 : 0 ≤ sint.Z i := hi1.1
    have hb2 : sint.Z i < sint.Z v.members'.len := by
      have e1 := hsl.1
      have e2 := hi'
      have e3 := hb1
      simp only [sint.nat, sint.Z] at e1 e2 e3 ⊢
      revert e1 e2 e3
      generalize BitVec.toInt i = a
      generalize BitVec.toInt v.members'.len = b
      intro e1 e2 e3; omega
    icases ownSlice_elem_acc (sint.Z i) _ v.members' (DFrac.own 1) ns hi1.1 hnv $$ Hm with ⟨Hel, Hmb⟩
    icases fpA.pev_fields _ _ _ $$ Hel with ⟨HPE, HV, Hpb⟩
    wp_auto
    simp only [hb1, hb2, _root_.and_self, ↓reduceIte]
    wp_auto
    ihave Hel := Hpb $$ HPE HV
    ihave Hm := Hmb $$ Hel
    rw [List.set_getElem_self] at *
    have hval : M k = some ns[(sint.Z i).toNat].Value' := by
      rw [hM, fpA.kvFind_some xs hnd]
      have hix : (sint.Z i).toNat < xs.length := by
        have := hi'; rw [hlen'] at this; simpa using this
      have h1 := congrArg (·[(sint.Z i).toNat]?) h.1
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hix,
        Option.map_some, Option.some.injEq] at h1
      have h2 : (xs.map (·.1))[(sint.Z i).toNat]? = some k := hk
      simp only [List.getElem?_map, List.getElem?_eq_getElem hix, Option.map_some,
        Option.some.injEq] at h2
      rw [h1, ← h2]
      exact List.getElem_mem hix
    iapply HΦ
    isplitl [Hf Hback Hm Hcap]
    · iexists _
      isplitl [Hback Hf]
      · iapply Hback; iexact Hf
      iexists ns, xs; iframe; isplit; iexact Hx; ipureintro; exact h
    ipureintro
    rw [hval]; exact ⟨rfl, rfl⟩
  case false =>
    have hn : pe ∉ xs.map (·.1) := fun hm => by
      have := (fpA.bs_found hw hp h.2.1 hbs).2 hm
      have := hf.2 this; simp at this
    have hval : M pe = none := by rw [hM]; exact (fpA.kvFind_none xs pe).2 hn
    wp_auto
    iapply HΦ
    isplitl [Hf Hback Hm Hcap]
    · iexists _
      isplitl [Hback Hf]
      · iapply Hback; iexact Hf
      iexists ns, xs; iframe; isplit; iexact Hx; ipureintro; exact h
    ipureintro
    rw [hval]; exact ⟨rfl, rfl⟩

end proof

end smd
end EtcdGrove
end Perennial
