/-
`fieldpath.PathElementMap.Insert`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Compare
public import Spec.slices.BinarySearchFunc
public import Spec.slices.Insert
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

theorem fieldpath.PathElementMap.Insert.wp_proof
    (h_PathElement_Compare : fieldpath.PathElement.Compare.spec (GF := GF))
    (h_slices_BinarySearchFunc : EtcdGrove.slices.BinarySearchFunc.spec (GF := GF))
    (h_slices_Insert : EtcdGrove.slices.Insert.spec (GF := GF)) :
    fieldpath.PathElementMap.Insert.spec (GF := GF) := fun l M e pe x => by
  wp_start as ⟨Hs, #He, %hc⟩
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
  have hcard : xs.length < 2 ^ 63 - 1 := hc _ (fpA.peMap_hasCard M xs hnd hM)
  cases found
  case true =>
    obtain ⟨k, hk, hc0⟩ := hf.1 rfl
    have hkw := hw k (List.mem_of_getElem? hk)
    have hke := (PE_compare_eq_zero_law_holds k pe hkw hp).1 hc0
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
    have hix : (sint.Z i).toNat < xs.length := by
      have := hi'; rw [hlen'] at this; simpa using this
    have hxk : xs[(sint.Z i).toNat]? = some (k, xs[(sint.Z i).toNat].2) := by
      rw [List.getElem?_eq_getElem hix]
      have h2 : (xs.map (·.1))[(sint.Z i).toNat]? = some k := hk
      simp only [List.getElem?_map, List.getElem?_eq_getElem hix, Option.map_some,
        Option.some.injEq] at h2
      rw [← h2]
    iapply HΦ
    iexists _
    isplitl [Hback Hf]
    · iapply Hback; iexact Hf
    iexists _, (xs.set (sint.Z i).toNat (k, x))
    iframe Hm Hcap
    have e1 : (ns.set (sint.Z i).toNat
        { PathElement' := ns[(sint.Z i).toNat].PathElement', Value' := x }).map (·.PathElement') =
        ns.map (·.PathElement') := by
      rw [List.map_set]
      rw [show ns[(sint.Z i).toNat].PathElement' =
        (ns.map (·.PathElement'))[(sint.Z i).toNat]'(by simpa using hi') by simp]
      exact List.set_getElem_self _
    have e2 : (xs.set (sint.Z i).toNat (k, x)).map (·.1) = xs.map (·.1) := by
      rw [List.map_set]
      have : k = (xs.map (·.1))[(sint.Z i).toNat]'(by simpa using hix) := by
        have h2 : (xs.map (·.1))[(sint.Z i).toNat]? = some k := hk
        rw [List.getElem?_eq_getElem (by simpa using hix)] at h2; exact (Option.some.inj h2).symm
      conv => lhs; rw [this]
      exact List.set_getElem_self _
    rw [e1, e2]
    isplit
    · iexact Hx
    ipureintro
    refine ⟨?_, h.2.1, ?_⟩
    · rw [List.map_set, List.map_set, h.1]
    · intro k'
      have := fpA.kvFind_set xs _ k _ x hnd hxk k'
      unfold fpA.kvFind at this
      rw [this]
      unfold PEMap.insert
      by_cases hk' : k' = k
      · simp [hk']
      · simp only [hk', ↓reduceIte]; exact hM k'
  case false =>
    have hn : pe ∉ xs.map (·.1) := fun hm => by
      have := (fpA.bs_found hw hp h.2.1 hbs).2 hm
      have := hf.2 this; simp at this
    wp_auto
    wp_apply (wp_slice_literal (V := fieldpath.pathElementValue) [{ PathElement' := e, Value' := x }])
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    wp_auto
    wp_apply (h_slices_Insert v.members' ns i _ [{ PathElement' := e, Value' := x }] (DFrac.own 1))
      $$ [$Hm $Hcap $Hosl] as %s' ⟨Hm, Hcap, -⟩
    · ipureintro; refine ⟨hi1.1, hi1.2, ?_⟩; simp only [List.length_singleton]; simp at hlen'; omega
    iapply HΦ
    iexists _
    isplitl [Hback Hf]
    · iapply Hback; iexact Hf
    iexists _, (xs.take (sint.Z i).toNat ++ [(pe, x)] ++ xs.drop (sint.Z i).toNat)
    iframe Hm Hcap
    have e1 : (ns.take (sint.Z i).toNat ++ [({ PathElement' := e, Value' := x } : fieldpath.pathElementValue)] ++
        ns.drop (sint.Z i).toNat).map (fun a : fieldpath.pathElementValue => a.PathElement') =
        (ns.map (·.PathElement')).take (sint.Z i).toNat ++ [e] ++ (ns.map (·.PathElement')).drop (sint.Z i).toNat := by
      simp [List.map_take, List.map_drop]
    have e2 : (xs.take (sint.Z i).toNat ++ [(pe, x)] ++ xs.drop (sint.Z i).toNat).map (·.1) =
        (xs.map (·.1)).take (sint.Z i).toNat ++ [pe] ++ (xs.map (·.1)).drop (sint.Z i).toNat := by
      simp [List.map_take, List.map_drop]
    rw [e1, e2]
    isplit
    · iapply fpA.isPEL_insert; iframe Hx He
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.map_append, List.map_take, List.map_drop, h.1]; rfl
    · have := fpA.bs_insert_sorted hw hp h.2.1 hbs hn
      simpa only [List.append_assoc, List.singleton_append] using this
    · intro k'
      have := fpA.kvFind_ins xs (sint.Z i).toNat pe x hnd hn k'
      unfold fpA.kvFind at this
      rw [this]
      unfold PEMap.insert
      by_cases hk' : k' = pe
      · simp [hk']
      · simp only [hk', ↓reduceIte]; exact hM k'

end proof

end smd
end EtcdGrove
end Perennial
