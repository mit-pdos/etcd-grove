/-
`fieldpath.SetNodeMap.Descend`: proved over its callees' specs (the hypotheses): the binary
search's index read over the children (`fpI.bs_found_cs`, `fpI.bs_notfound_cs`); the child lent
out with the way back (`fpI.trieOwnC_at`), or a new empty one inserted (`fpI.trieOwnC_ins`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Descend
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Compare
public import Spec.slices.BinarySearchFunc
public import Spec.slices.Insert
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsInsert

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

theorem fieldpath.SetNodeMap.Descend.wp_proof
    (h_PathElement_Compare : fieldpath.PathElement.Compare.spec (GF := GF))
    (h_slices_BinarySearchFunc : EtcdGrove.slices.BinarySearchFunc.spec (GF := GF))
    (h_slices_Insert : EtcdGrove.slices.Insert.spec (GF := GF)) :
    fieldpath.SetNodeMap.Descend.spec (GF := GF) := fun l cs e pe => by
  wp_start as ⟨Hn, #He, %hs⟩
  unfold ownNodesT
  icases Hn with ⟨%m, %ns, Hl, Hm, Hcap, Hc⟩
  icases fpI.trieOwnC_keys ns cs $$ Hc with ⟨#Hk, Hc⟩
  icases fpI.nodemap_members_upd l m (DFrac.own 1) $$ Hl with ⟨Hf, Hback⟩
  let es := ns.map (·.pathElement')
  ihave %hmd := fpA.isPEL_mdl es (fpI.ckeys cs) pe $$ Hk
  ihave %hw := fpL.isPEL_wf es (fpI.ckeys cs) $$ Hk
  ihave %hlen := fpL.isPEL_length es (fpI.ckeys cs) $$ Hk
  ihave %hp := fpL.isPE_wf' e pe $$ He
  let mm : fieldpath.setNode → PE := fun a => fpA.mdl es (fpI.ckeys cs) pe a.pathElement'
  have hmd' : ∀ (k : Nat) (a : fieldpath.setNode), ns[k]? = some a → (fpI.ckeys cs)[k]? = some (mm a) :=
    fun k a hk => hmd k a.pathElement' (by simp [es, List.getElem?_map, hk])
  have hlen' : ns.length = (fpI.ckeys cs).length := by simpa [es] using hlen
  wp_auto
  wp_apply (h_slices_BinarySearchFunc (E := fieldpath.setNode) fieldpath.PathElement.ty m.members' ns
    (DFrac.own 1) e _ (fun a => PE.compare (mm a) pe) iprop(True))
    $$ [$Hm] as %i %found ⟨Hm, -, %hi1, %hi2, %hi3⟩
  · isplitr
    · itrivial
    isplit
    · imodintro
      iintro %a %ha
      imodintro
      iintro %Φ' - HΦ'
      have hka : es[fpA.peIdx es a.pathElement']? = some a.pathElement' :=
        fpA.peIdx_get es a.pathElement' (List.mem_map_of_mem ha)
      ihave ⟨%x, %hx, #Ha⟩ := fpL.isPEL_lookup es (fpI.ckeys cs) _ a.pathElement' hka $$ Hk
      have hx' : x = mm a := by
        have := hmd _ a.pathElement' hka; rw [hx] at this; exact Option.some.inj this
      subst hx'
      wp_auto
      wp_method_call; wp_call; wp_auto
      wp_apply (h_PathElement_Compare a.pathElement' e (mm a) pe) $$ [$Ha $He] as %r %hr
      iapply HΦ'
      iframe
      ipureintro; exact ⟨trivial, hr⟩
    · ipureintro
      intro k j ek ej hk hj hkj
      exact fpA.sorted_signum hw hp hs.1 k j _ _ (hmd' k ek hk) (hmd' j ej hj) hkj
  obtain ⟨hbs, hf⟩ := fpA.bs_transfer ns (fpI.ckeys cs) pe mm hmd' hlen' _ found hi1 hi2 hi3
  cases found
  · have hnot : pe ∉ fpI.ckeys cs := fun hm => by
      have := hf.2 ((fpA.bs_found hw hp hs.1 hbs).2 hm); simp at this
    obtain ⟨hnone, hins⟩ := fpI.bs_notfound_cs hw hp hs.1 hbs hnot
    ihave %hsl := ownSlice_len $$ Hm
    have hcl : ns.length = cs.length := by rw [hlen']; simp [fpI.ckeys]
    wp_auto
    let n0 : fieldpath.setNode := { pathElement' := e, set' := «$v1_ptr» }
    wp_apply (wp_slice_literal (V := fieldpath.setNode) [n0])
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    wp_auto
    wp_apply (h_slices_Insert m.members' ns i _ [n0] (DFrac.own 1)) $$ [$Hm $Hcap $Hosl] as %s' ⟨Hm, Hcap, -⟩
    · ipureintro; refine ⟨hi1.1, hi1.2, ?_⟩; simp; omega
    have hil : (sint.Z i).toNat ≤ ns.length := by omega
    have hlk : (ns.take (sint.Z i).toNat ++ [n0] ++ ns.drop (sint.Z i).toNat)[(sint.Z i).toNat]? = some n0 := by
      have htl : (ns.take (sint.Z i).toNat).length = (sint.Z i).toNat := List.length_take_of_le hil
      rw [List.append_assoc, List.getElem?_append_right (by rw [htl]; exact Nat.le_refl _), htl, Nat.sub_self]
      rfl
    ihave %hsl' := ownSlice_len $$ Hm
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s'.len := by
      refine ⟨hi1.1, ?_⟩
      have h3 : (sint.Z i).toNat < sint.nat s'.len := by rw [← hsl'.1]; simp; omega
      simp only [sint.nat] at h3
      have key : ∀ a b : Int, a.toNat < b.toNat → a < b := by intro a b h; omega
      exact key _ _ h3
    icases ownSlice_elem_acc (sint.Z i) n0 s' (DFrac.own 1) _ hi1.1 hlk $$ Hm with ⟨Hel, Hmb⟩
    icases fpI.setnode_fields _ n0 (DFrac.own 1) $$ Hel with ⟨Hpf, Hsf, Hel⟩
    rw [if_pos hb]
    wp_auto
    ihave Hel := Hel $$ Hpf Hsf
    ihave Hm := Hmb $$ Hel
    ihave Hl := Hback $$ Hf
    ihave Ht := fpI.trieOwn_empty «$v1_ptr» $$ «$v1»
    have hns : (ns.take (sint.Z i).toNat ++ [n0] ++ ns.drop (sint.Z i).toNat).set (sint.Z i).toNat n0 =
        ns.take (sint.Z i).toNat ++ n0 :: ns.drop (sint.Z i).toNat := by
      rw [List.append_assoc, List.singleton_append]
      have hlk' : (ns.take (sint.Z i).toNat ++ n0 :: ns.drop (sint.Z i).toNat)[(sint.Z i).toNat]? = some n0 := by
        rw [← List.singleton_append, ← List.append_assoc]; exact hlk
      apply List.ext_getElem?; intro k
      rw [List.getElem?_set]
      split
      · next h => subst h; rw [hlk']; simp only [if_pos (List.getElem?_eq_some_iff.1 hlk').1]
      · rfl
    rw [hns]
    iapply HΦ
    iexists Trie.empty
    isplitr
    · ipureintro; exact Or.inr ⟨hnone, rfl⟩
    iframe Ht
    iintro %t' Ht'
    iexists { members' := s' }, (ns.take (sint.Z i).toNat ++ n0 :: ns.drop (sint.Z i).toNat)
    iframe
    rw [hins]
    iapply (fpI.trieOwnC_ins ns cs (sint.Z i).toNat n0 pe t')
    iframe
    iexact He
  · obtain ⟨t, hct, hlk, hset⟩ := fpI.bs_found_cs hw hp hbs (hf.1 rfl)
    have hil : (sint.Z i).toNat < ns.length := by
      rw [hlen']; simp [fpI.ckeys]; exact (List.getElem?_eq_some_iff.1 hct).1
    obtain ⟨n, hn⟩ : ∃ n, ns[(sint.Z i).toNat]? = some n := ⟨_, List.getElem?_eq_getElem hil⟩
    ihave %hsl := ownSlice_len $$ Hm
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z m.members'.len := by
      refine ⟨hi1.1, ?_⟩
      have h3 : (sint.Z i).toNat < sint.nat m.members'.len := hsl.1 ▸ hil
      simp only [sint.nat] at h3
      have key : ∀ a b : Int, a.toNat < b.toNat → a < b := by intro a b h; omega
      exact key _ _ h3
    have hns : ns.set (sint.Z i).toNat n = ns := by
      apply List.ext_getElem?; intro k
      rw [List.getElem?_set]
      split
      · next h => subst h; rw [hn]
      · rfl
    icases ownSlice_elem_acc (sint.Z i) n m.members' (DFrac.own 1) ns hi1.1 hn $$ Hm with ⟨Hel, Hmb⟩
    icases fpI.setnode_fields _ n (DFrac.own 1) $$ Hel with ⟨Hpf, Hsf, Hel⟩
    wp_auto
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_auto
    ihave Hel := Hel $$ Hpf Hsf
    ihave Hm := Hmb $$ Hel
    rw [hns]
    ihave Hl := Hback $$ Hf
    icases fpI.trieOwnC_at ns cs (sint.Z i).toNat n pe t hn hct $$ Hc with ⟨Ht, Hw⟩
    iapply HΦ
    iexists t
    isplitr
    · ipureintro; exact Or.inl hlk
    iframe Ht
    iintro %t' Ht'
    iexists { members' := m.members' }, ns
    iframe
    rw [hset]
    iapply Hw; iexact Ht'

end proof

end smd
end EtcdGrove
end Perennial
