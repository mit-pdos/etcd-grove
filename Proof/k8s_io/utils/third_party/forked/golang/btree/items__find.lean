module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.items__find
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Lemmas.Low
public import Perennial.Proof.sort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem items.find.wp_proof : items.find.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o sl is dq item k less Hsorted
  unfold isLess allItems
  wp_start as ⟨Hsl, #Hless, #Hitem, #Hall⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_map] at Hlen
  wp_auto
  ipersist s
  ipersist less
  ipersist item
  wp_apply sort.wp_Search _ _ (findPred o.lt is k) iprop(sl ↦*{dq} is.map Prod.fst) $$ [Hsl]
  · iframe Hsl
    isplitl []
    · ipureintro; exact Hlen.2
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨Hsl, %Hb⟩
      wp_auto
      list_elem is (sint.nat i) as e
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hb.1, by word⟩)]
      wp_apply wp_load_slice_index sl (sint.Z i) _ dq e.1 Hb.1 $$ [Hsl] as Hsl
      · iframe; ipureintro
        rw [show (sint.Z i).toNat = sint.nat i from rfl, List.getElem?_map, He_lookup]; rfl
      ihave #He := Hall $$ %e %(List.mem_of_getElem? He_lookup)
      wp_apply Hless $$ %item %e.1 %k %e.2 [] as %r %Hr
      · isplit
        · iexact Hitem
        · iexact He
      iapply HΦ
      iframe
      ipureintro
      have := findPred_eq o.lt is k (sint.Z i) e He_lookup
      cases r <;> cases hf : findPred o.lt is k (sint.Z i) <;> simp_all
    · ipureintro
      intro a b Hab Hfa
      list_elem is a.toNat as ea
      list_elem is b.toNat as eb
      rw [findPred_eq o.lt is k _ _ Hea_lookup] at Hfa
      rw [findPred_eq o.lt is k _ _ Heb_lookup]
      rcases List.getElem?_eq_some_iff.mp Hea_lookup with ⟨ha, rfl⟩
      rcases List.getElem?_eq_some_iff.mp Heb_lookup with ⟨hb, rfl⟩
      exact o.order.trans _ _ _ Hfa (sorted_lt_getElem o.lt Hsorted ha hb (by omega))
  iintro %i ⟨Hsl, %Hi_nn, %Hfound, %Hoob, %Hgt⟩
  wp_auto
  have hle : sint.Z i ≤ sint.Z sl.len := by
    refine Classical.byContradiction fun hc => ?_
    have := Hoob (fun j hj => Hgt j ⟨hj.1, by omega⟩)
    omega
  have hn : sint.nat i ≤ is.length := by word
  have hbelow : ∀ j (h : j < sint.nat i), ¬ o.lt k (is[j]'(by omega)).2 := by
    intro j h hlt
    have h1 := Hgt (j : Int) ⟨by omega, by word⟩
    have h2 := (findPred_eq o.lt is k (j : Int) is[j] (by simp)).mpr hlt
    rw [h1] at h2
    exact absurd h2 (by decide)
  have habove : ∀ (h : sint.nat i < is.length), o.lt k is[sint.nat i].2 := by
    intro h
    exact (findPred_eq o.lt is k _ is[sint.nat i] (by simp)).mp (Hfound (by word))
  wp_if_destruct
  · rw [show sint.Z (W64 0) = 0 from rfl] at Hif
    have hpos : 0 < sint.nat i := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    have hp : sint.nat (i - W64 1) = sint.nat i - 1 := by word
    have hlk : (is.map Prod.fst)[(sint.Z (i - W64 1)).toNat]? =
        some (is[sint.nat i - 1]'(by word)).1 := by
      rw [show (sint.Z (i - W64 1)).toNat = sint.nat (i - W64 1) from rfl, hp, List.getElem?_map,
        List.getElem?_eq_getElem (by word)]; rfl
    wp_apply wp_load_slice_index sl (sint.Z (i - W64 1)) _ dq _ (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hlk
    ihave #He := Hall $$ %(is[sint.nat i - 1]'(by word)) %(List.getElem_mem _)
    wp_apply Hless $$ %_ %item %_ %k [] as %r %Hr
    · isplit
      · iexact He
      · iexact Hitem
    cases r
    · wp_auto
      obtain ⟨hc, hf⟩ := find_found o.lt o.order is k Hsorted (sint.nat i) hn hpos hbelow
        (by simp at Hr; exact Hr)
      iapply HΦ
      iframe
      ipureintro
      rw [hp]
      exact ⟨hc.symm, by word, by simpa using hf⟩
    · wp_auto
      obtain ⟨hc, hf⟩ := find_notfound o.lt o.order is k Hsorted (sint.nat i) hn habove
        (fun _ => by simpa using Hr)
      iapply HΦ
      iframe
      ipureintro
      exact ⟨hc.symm, Hi_nn, by simpa using hf⟩
  · obtain ⟨hc, hf⟩ := find_notfound o.lt o.order is k Hsorted (sint.nat i) hn habove
      (fun h => by exfalso; word)
    iapply HΦ
    iframe
    ipureintro
    exact ⟨hc.symm, Hi_nn, by simpa using hf⟩

end proof

end btree
end EtcdGrove
end Perennial
