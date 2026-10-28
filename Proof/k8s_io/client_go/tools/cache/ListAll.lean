/-
Proof of `Spec/k8s_io/client_go/tools/cache/ListAll.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.ListAll
public import Spec.k8s_io.client_go.tools.cache.cache__List

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem ListAll.wp_proof (wp_List : cache.List.spec (GF := GF) (hG := hG)) :
    ListAll.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam kf sel af A
  iintro %Φ ⟨#Hpkg, #Hca, Hr, #Hsel, #Haf, HA⟩ HAU
  iunfold everySel at Hsel
  icases Hsel with ⟨%i, %hi, #Hmn, #Hempty⟩
  iunfold appendOk at Haf
  subst hi
  wp_func_call
  wp_call
  (try wp_auto)
  wp_apply Hmn
  (try wp_auto)
  wp_apply Hempty
  (try wp_auto)
  wp_bind
  iapply (wp_List ca ts γ OK Fam kf) $$ [$Hpkg $Hca $Hr]
  inext
  imod HAU with ⟨%σ, ⟨Hst, %hnn⟩, Hcl⟩
  imodintro
  iexists σ
  iframe Hst
  iintro Hst
  imod Hcl $$ [Hst] with HK
  · iframe; ipureintro; exact hnn
  imodintro
  iintro %sl ⟨%ks, %Hks, Hsl, #Hoks, Hr⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  (try wp_auto)
  ihave IH : iprop(∃ (n : w64) (x : GoInterface),
      "i" ∷ i_ptr ↦ n ∗
      "m" ∷ m_ptr ↦ x ∗
      "HA" ∷ A ((ks.map (objAt σ.items)).take (sint.nat n)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ks.length⌝) $$ [i m HA]
  · iexists W64 0, _
    iframe
    ipureintro
    exact ⟨by decide, by simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ks.length := by rw [List.length_map] at Hlen; word
    obtain ⟨k, Hk⟩ : ∃ k, ks[sint.nat n]? = some k := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have He : (ks.map (objAt σ.items))[sint.nat n]? = some (objAt σ.items k) := by
      rw [List.getElem?_map, Hk]; rfl
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) _ (DFrac.own 1) _ Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact He
    have hkin : k ∈ σ.items := (Hks.2 k).1 (List.mem_of_getElem? Hk)
    ihave #Hok1 := BigSepL.bigSepL_lookup (Φ := fun _ o => iprop(okNil OK o)) He $$ Hoks
    ihave #HOKm := okNil_noNil OK σ.items k hnn hkin $$ Hok1
    (try wp_auto)
    ihave #Haf1 := Haf $$ %((ks.map (objAt σ.items)).take (sint.nat n)) %(objAt σ.items k)
    wp_bind (App (Val #af) (Val #(objAt σ.items k)))
    iapply Haf1 $$ [$HA $HOKm]
    inext
    iintro HA
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, _
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
      have := Hn.1; have := Hlt; have := Hlen.1; word
    have h2 : sint.nat (n + W64 1) ≤ ks.length := by rw [hn1]; omega
    have h1 : 0 ≤ sint.Z (n + W64 1) := by have := Hn.1; have := Hlt; have := Hlen.1; word
    rw [hn1, List.take_add_one, He]
    simp only [Option.toList_some]
    iframe
    ipureintro
    exact ⟨h1, by omega⟩
  · rw [List.length_map] at Hlen
    have hnl : sint.nat n = ks.length := by word
    have htk : (ks.map (objAt σ.items)).take (sint.nat n) = ks.map (objAt σ.items) := by
      rw [hnl, ← List.length_map (f := objAt σ.items), List.take_length]
    rw [htk]
    (try wp_auto)
    iapply HK
    iexists ks
    iframe
    ipureintro; exact Hks

end proof

end cache
end EtcdGrove
end Perennial
