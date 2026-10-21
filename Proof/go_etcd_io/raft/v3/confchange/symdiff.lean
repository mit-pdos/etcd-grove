/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/symdiff.lean`. Lean-first (no Rocq counterpart).
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

/-- What the loop over one pair counts: the ids of `src` not in `other`, in any order. -/
theorem symdiff_count (src other : GMap w64 Unit) (keys : List w64)
    (Hkset : ∀ k, k ∈ keys ↔ (src !! k).isSome) (Hnd : keys.Nodup) :
    (keys.filter (fun k => !(other !! k).isSome)).length = GMap.size (src \ other) := by
  symm
  apply GMap.size_eq_length
  · exact Hnd.filter _
  · intro k
    rw [List.mem_filter, Hkset, GMap.lookup_sdiff]
    cases (other !! k).isSome <;> simp

theorem symdiff_take_succ (other : GMap w64 Unit) (keys : List w64) (i : Int) (key : w64)
    (Hi : 0 ≤ i) (Hkey : keys[i.toNat]? = some key) :
    ((keys.take (i + 1).toNat).filter (fun k => !(other !! k).isSome)).length =
      ((keys.take i.toNat).filter (fun k => !(other !! k).isSome)).length +
        (if (other !! key).isSome then 0 else 1) := by
  rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]
  simp only [Option.toList_some, List.filter_append, List.length_append]
  rcases h : other !! key with _ | v <;> simp [h]

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
  -- `for _, p := range pairs`: pair 0 counts the ids of `l` not in `r`, pair 1 those of
  -- `r` not in `l`
  ihave IH : iprop(∃ (n nv : w64) (pv : GoArray GoMap 2),
      "i" ∷ i_ptr ↦ n ∗
      "n" ∷ n_ptr ↦ nv ∗
      "p" ∷ p_ptr ↦ pv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 2 ∧ (sint.Z n = 0 → nv = W64 0) ∧
        (sint.Z n = 1 → nv = W64 (GMap.size (ml \ mr) : Int)) ∧
        (sint.Z n = 2 → nv = W64 (symdiffN ml mr : Int))⌝)
    $$ [i n p]
  · iexists W64 0, zero_val w64, zero_val (GoArray GoMap 2)
    iframe
    ipureintro
    refine ⟨by decide, by decide, fun _ => rfl, fun h => absurd h (by decide),
      fun h => absurd h (by decide)⟩
  wp_for IH
  wp_if_destruct
  · have Hcase : sint.nat n = 0 ∨ sint.nat n = 1 := by word
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 2) := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self]
    rcases Hcase with Hc | Hc
    · -- pair `{l, r}`
      have Hnv0 : nv = W64 0 := Hn.2.2.1 (by word)
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
          "%Hnv" ∷ ⌜nv' = W64 (((keys.take i.toNat).filter
            (fun k => !(mr !! k).isSome)).length : Int)⌝)) $$ Hl
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [id n Hr Hp1]
      · iexists zero_val w64, nv
        iframe
        ipureintro; exact ⟨Int.le_refl _, by simpa using Hnv0⟩
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
        iNamed HP
        wp_auto
        wp_apply wp_map_lookup2 $$ Hr as Hr
        have Hstep := symdiff_take_succ mr keys i key Hi Hkey
        wp_if_destruct
        · unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, _
          iframe
          ipureintro
          refine ⟨by omega, ?_⟩
          rw [Hstep, Hnv]
          cases h : (mr !! key).isSome <;> simp_all
        · unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, _
          iframe
          ipureintro
          refine ⟨by omega, ?_⟩
          rw [Hstep, Hnv]
          have h : (mr !! key).isSome = false := by simpa using Hif
          rw [h]
          simp only [Bool.false_eq_true, ↓reduceIte]
          word
      iintro HP Hl
      iNamed HP
      ihave p := Hpback $$ Hp1
      wp_for_post
      iframe
      iexists n + W64 1, nv', _
      iframe
      ipureintro
      have Hall : (keys.take (GMap.size ml : Int).toNat) = keys := by
        rw [Int.toNat_natCast, ← Hklen, List.take_length]
      rw [Hall, symdiff_count ml mr keys Hkset Hknodup] at Hnv
      refine ⟨by word, by word, fun h => absurd h (by word), fun _ => Hnv,
        fun h => absurd h (by word)⟩
    · -- pair `{r, l}`
      have Hnv1 : nv = W64 (GMap.size (ml \ mr) : Int) := Hn.2.2.2.1 (by word)
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
          "%Hnv" ∷ ⌜nv' = nv + W64 (((keys.take i.toNat).filter
            (fun k => !(ml !! k).isSome)).length : Int)⌝)) $$ Hr
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [id n Hl Hp1]
      · iexists zero_val w64, nv
        iframe
        ipureintro; refine ⟨Int.le_refl _, ?_⟩
        simp
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
        iNamed HP
        wp_auto
        wp_apply wp_map_lookup2 $$ Hl as Hl
        have Hstep := symdiff_take_succ ml keys i key Hi Hkey
        wp_if_destruct
        · unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, _
          iframe
          ipureintro
          refine ⟨by omega, ?_⟩
          rw [Hstep, Hnv]
          cases h : (ml !! key).isSome <;> simp_all
        · unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, _
          iframe
          ipureintro
          refine ⟨by omega, ?_⟩
          rw [Hstep, Hnv]
          have h : (ml !! key).isSome = false := by simpa using Hif
          rw [h]
          simp only [Bool.false_eq_true, ↓reduceIte]
          word
      iintro HP Hr
      iNamed HP
      ihave p := Hpback $$ Hp1
      wp_for_post
      iframe
      iexists n + W64 1, nv', _
      iframe
      ipureintro
      have Hall : (keys.take (GMap.size mr : Int).toNat) = keys := by
        rw [Int.toNat_natCast, ← Hklen, List.take_length]
      rw [Hall, symdiff_count mr ml keys Hkset Hknodup, Hnv1] at Hnv
      refine ⟨by word, by word, fun h => absurd h (by word), fun h => absurd h (by word),
        fun _ => ?_⟩
      rw [Hnv]
      unfold symdiffN
      word
  · -- `return n`
    have : sint.Z n = 2 := by word
    rw [Hn.2.2.2.2 this]
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
