/-
Proof of `Spec/confchange_symdiff.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.symdiff

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem confchange.symdiff.wp_proof : confchange.symdiff.spec (GF := GF) (hG := hG) := by
  intro l r ml mr dql dqr
  wp_start as ⟨Hl, Hr⟩
  wp_auto
  -- `pairs := [][2]MajorityConfig{{l, r}, {r, l}}`
  wp_apply wp_slice_literal (V := GoArray GoMap 2) [array.mk 2 [l, r], array.mk 2 [r, l]]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hslcap⟩
  simp only [go.arrayLiteralSize, List.foldl]
  rw [show (max (max ((0 : Int) + 1 + 1) 0) 0) = 2 by decide]
  wp_auto
  -- `for _, p := range pairs`: pair 0 counts the ids of `l` not in `r` (none, under
  -- `l ⊆ r`), pair 1 the ids of `r` not in `l` (at most `x`). Everything is said under
  -- the two premises of the postcondition.
  ihave IH : iprop(∃ (n nv : w64) (pv : GoArray GoMap 2),
      "i" ∷ i_ptr ↦ n ∗
      "n" ∷ n_ptr ↦ nv ∗
      "p" ∷ p_ptr ↦ pv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 2 ∧
        ((∀ k, (ml !! k).isSome → (mr !! k).isSome) →
          ∀ x, (∀ k, (mr !! k).isSome → (ml !! k).isSome ∨ k = x) →
          (sint.Z n ≤ 1 → nv = W64 0) ∧ (sint.Z n = 2 → 0 ≤ sint.Z nv ∧ sint.Z nv ≤ 1))⌝)
    $$ [i n p]
  · iexists W64 0, zero_val w64, zero_val (GoArray GoMap 2)
    iframe
    ipureintro
    refine ⟨by decide, by decide, fun _ _ _ => ⟨fun _ => rfl, fun h => absurd h (by decide)⟩⟩
  wp_for IH
  wp_if_destruct
  · have Hcase : sint.nat n = 0 ∨ sint.nat n = 1 := by word
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 2) := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self]
    rcases Hcase with Hc | Hc
    · -- pair `{l, r}`: `n` counts the ids of `l` not in `r`; none under `l ⊆ r`
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ (array.mk 2 [l, r]) Hn.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro
        show [array.mk 2 [l, r], array.mk 2 [r, l]][sint.nat n]? = _; rw [Hc]; rfl
      icases array_acc _ (sint.Z (W64 0)) _ _ _ l (by decide) rfl $$ p with ⟨Hp0, Hpback⟩
      wp_auto
      ihave p := Hpback $$ Hp0
      icases array_acc _ (sint.Z (W64 1)) _ _ _ r (by decide) rfl $$ p with ⟨Hp1, Hpback⟩
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x nv' : w64),
          "%Hi" ∷ ⌜0 ≤ i⌝ ∗
          "id" ∷ id_ptr ↦ x ∗
          "n" ∷ n_ptr ↦ nv' ∗
          "Hr" ∷ r ↦${dqr} mr ∗
          "Hp1" ∷ arrayIndexRef GoMap (sint.Z (W64 1)) p_ptr ↦ r ∗
          "%Hnv" ∷ ⌜(∀ k, (ml !! k).isSome → (mr !! k).isSome) → nv' = nv⌝)) $$ Hl
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [id n Hr Hp1]
      · iexists zero_val w64, nv
        iframe
        ipureintro; exact ⟨Int.le_refl _, fun _ => rfl⟩
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
        iNamed HP
        wp_auto
        wp_apply wp_map_lookup2 $$ Hr as Hr
        wp_if_destruct
        · -- `key ∈ r`: nothing to count
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, _
          iframe
          ipureintro
          exact ⟨by omega, fun H1 => Hnv H1⟩
        · -- `key ∉ r`: `n++`, only without the premise
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, _
          iframe
          ipureintro
          exact ⟨by omega, fun H1 => absurd (H1 key (by rw [Hvv]; rfl)) Hif⟩
      iintro HP Hl
      iNamed HP
      ihave p := Hpback $$ Hp1
      wp_for_post
      iframe
      iexists n + W64 1, nv', _
      iframe
      ipureintro
      refine ⟨by word, by word, fun H1 x H2 => ⟨fun _ => ?_, fun h => absurd h (by word)⟩⟩
      rw [Hnv H1]
      exact (Hn.2.2 H1 x H2).1 (by word)
    · -- pair `{r, l}`: `n` counts the ids of `r` not in `l`; at most one, `x`
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ (array.mk 2 [r, l]) Hn.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro
        show [array.mk 2 [l, r], array.mk 2 [r, l]][sint.nat n]? = _; rw [Hc]; rfl
      icases array_acc _ (sint.Z (W64 0)) _ _ _ r (by decide) rfl $$ p with ⟨Hp0, Hpback⟩
      wp_auto
      ihave p := Hpback $$ Hp0
      icases array_acc _ (sint.Z (W64 1)) _ _ _ l (by decide) rfl $$ p with ⟨Hp1, Hpback⟩
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x nv' : w64),
          "%Hi" ∷ ⌜0 ≤ i⌝ ∗
          "id" ∷ id_ptr ↦ x ∗
          "n" ∷ n_ptr ↦ nv' ∗
          "Hl" ∷ l ↦${dql} ml ∗
          "Hp1" ∷ arrayIndexRef GoMap (sint.Z (W64 1)) p_ptr ↦ l ∗
          "%Hnv" ∷ ⌜(∀ k, (ml !! k).isSome → (mr !! k).isSome) →
            ∀ x, (∀ k, (mr !! k).isSome → (ml !! k).isSome ∨ k = x) →
            0 ≤ sint.Z nv' ∧ sint.Z nv' ≤ 1 ∧ (sint.Z nv' = 1 → x ∈ keys.take i.toNat)⌝))
        $$ Hr
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [id n Hl Hp1]
      · iexists zero_val w64, nv
        iframe
        ipureintro
        refine ⟨Int.le_refl _, fun H1 x H2 => ?_⟩
        have h0 := (Hn.2.2 H1 x H2).1 (by word)
        rw [h0]
        refine ⟨by decide, by decide, fun h => absurd h (by decide)⟩
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
        iNamed HP
        wp_auto
        wp_apply wp_map_lookup2 $$ Hl as Hl
        wp_if_destruct
        · -- `key ∈ l`: nothing to count
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, _
          iframe
          ipureintro
          refine ⟨by omega, fun H1 x H2 => ?_⟩
          obtain ⟨h0, h1, h2⟩ := Hnv H1 x H2
          refine ⟨h0, h1, fun h => ?_⟩
          rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]
          exact List.mem_append_left _ (h2 h)
        · -- `key ∉ l`: `key = x`, and it is the first such key
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, _
          iframe
          ipureintro
          refine ⟨by omega, fun H1 x H2 => ?_⟩
          obtain ⟨h0, h1, h2⟩ := Hnv H1 x H2
          have Hkx : key = x := by
            rcases H2 key (by rw [Hvv]; rfl) with h | h
            · exact absurd h Hif
            · exact h
          have Hnv0 : sint.Z nv' = 0 := by
            rcases (show sint.Z nv' = 0 ∨ sint.Z nv' = 1 by omega) with h | h
            · exact h
            · exfalso
              have := h2 h
              rw [← Hkx] at this
              exact not_mem_take_of_nodup Hknodup Hkey this
          refine ⟨by word, by word, fun _ => ?_⟩
          rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey, ← Hkx]
          exact List.mem_append_right _ (List.mem_singleton.2 rfl)
      iintro HP Hr
      iNamed HP
      ihave p := Hpback $$ Hp1
      wp_for_post
      iframe
      iexists n + W64 1, nv', _
      iframe
      ipureintro
      refine ⟨by word, by word, fun H1 x H2 => ⟨fun h => absurd h (by word), fun _ => ?_⟩⟩
      obtain ⟨h0, h1, -⟩ := Hnv H1 x H2
      exact ⟨h0, h1⟩
  · -- `return n`
    iapply HΦ
    iframe
    ipureintro
    intro H1 x H2
    exact (Hn.2.2 H1 x H2).2 (by word)

end proof

end EtcdGrove
end Perennial
