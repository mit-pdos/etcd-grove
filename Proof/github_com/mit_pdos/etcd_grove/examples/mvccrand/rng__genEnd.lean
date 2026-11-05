/- Lean-first (no Rocq counterpart). The proof of `rng.genEnd`: the four arms of its switch. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__intn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem rng.genEnd.wp_proof (wp_intn : rng.intn.spec (GF := GF) (hG := hG))
    (wp_genKey : rng.genKey.spec (GF := GF) (hG := hG)) :
    rng.genEnd.spec (GF := GF) (hG := hG) := by
  intro r g
  wp_start as Hr
  wp_auto
  wp_apply wp_intn r g (W64 6) (by decide) $$ [$Hr] as %x ⟨⟨%g1, Hr⟩, %Hx⟩
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iframe
    iexists []
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    ipureintro; exact ⟨Or.inl rfl, fun _ => rfl⟩
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      iframe
      iexists []
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      ipureintro; exact ⟨Or.inl rfl, fun _ => rfl⟩
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        iapply HΦ
        iframe
        iexists []
        isplitl
        · iapply ownSlice_nil
        isplitl
        · iapply ownSliceCap_nil
        ipureintro; exact ⟨Or.inl rfl, fun _ => rfl⟩
      · (try wp_auto)
        wp_if_destruct
        · -- `[]byte{}`
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sp ⟨Hs, Hcap⟩
          (try wp_auto)
          iapply HΦ
          iframe
          ipureintro
          exact ⟨Or.inl rfl, fun _ => rfl⟩
        · (try wp_auto)
          wp_if_destruct
          · -- an extra end
            ihave Hmi : (mvccrandInit : IProp GF) $$ []
            · iapply isPkgInit_access $$ Hpkg
            iunfold mvccrandInit at Hmi
            icases Hmi with ⟨-, ⟨%es, #Hes, #Hesl⟩⟩
            ihave %Hesn := ownSlice_len $$ Hesl
            have hes2 : sint.Z es.len = 2 := by
              have h := Hesn.1; simp only [extraEndList, List.length_cons, List.length_nil] at h
              have h4 : sint.nat es.len = (sint.Z es.len).toNat := rfl
              have := Hesn.2; omega
            (try wp_auto)
            wp_apply wp_intn _ _ es.len (by omega) $$ [$Hr] as %y ⟨Hr, %Hy⟩
            have hyl : (sint.Z y).toNat < extraEndList.length := by simp [extraEndList]; omega
            have hb : 0 ≤ sint.Z y ∧ sint.Z y < sint.Z es.len := ⟨Hy.1, by omega⟩
            (try wp_auto)
            (try simp only [hb, _root_.and_self, ↓reduceIte])
            wp_apply wp_load_slice_index es (sint.Z y) extraEndList DFrac.discard
              (extraEndList[(sint.Z y).toNat]'hyl) Hy.1 $$ [Hesl] as -
            · iframe #; ipureintro; exact List.getElem?_eq_getElem hyl
            (try wp_auto)
            wp_apply wp_string_to_bytes as %sl ⟨Hsl, Hcap⟩
            (try wp_auto)
            ihave %Hsn := ownSlice_len $$ Hsl
            iapply HΦ
            iframe
            ipureintro
            refine ⟨Or.inr (Or.inl (List.getElem_mem hyl)), fun h => ?_⟩
            subst h
            have : extraEndList[(sint.Z y).toNat]'hyl ≠ [] := by
              have : (sint.Z y).toNat = 0 ∨ (sint.Z y).toNat = 1 := by simp [extraEndList] at hyl; omega
              rcases this with h | h <;> simp [extraEndList, h]
            exact absurd (List.eq_nil_of_length_eq_zero (by rw [Hsn.1]; rfl)) this
          · -- a key
            (try wp_auto)
            wp_apply wp_genKey _ _ $$ [$Hr] as %sl ⟨Hr, %k, Hsl, Hcap, %Hk⟩
            (try wp_auto)
            ihave %Hsn := ownSlice_len $$ Hsl
            iapply HΦ
            iframe
            ipureintro
            refine ⟨Or.inr (Or.inr Hk), fun h => ?_⟩
            subst h
            have : k ≠ [] := by
              intro h0; subst h0; simp [keyList] at Hk
            exact absurd (List.eq_nil_of_length_eq_zero (by rw [Hsn.1]; rfl)) this

end proof

end mvccrand
end EtcdGrove
end Perennial
