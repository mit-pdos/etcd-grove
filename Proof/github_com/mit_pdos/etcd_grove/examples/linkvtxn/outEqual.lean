/-
Lean-first (no Rocq counterpart).

The proof of `outEqual`: by the kind; a list's key-values and a transaction's results, each
loop's invariant that the pairs before the index compare equal.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.outEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.vrEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.resEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.kvsOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.resOf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem zip_take_succ {α : Type} (Q : α × α → Bool) (l1 l2 : List α) (j : Nat) (x y : α)
    (h1 : l1[j]? = some x) (h2 : l2[j]? = some y) :
    ((l1.take (j + 1)).zip (l2.take (j + 1))).all Q =
      (((l1.take j).zip (l2.take j)).all Q && Q (x, y)) := by
  have hl1 : j < l1.length := (List.getElem?_eq_some_iff.1 h1).1
  have hl2 : j < l2.length := (List.getElem?_eq_some_iff.1 h2).1
  rw [List.take_add_one, List.take_add_one, h1, h2]
  simp only [Option.toList_some]
  rw [List.zip_append (by simp only [List.length_take]; omega)]
  simp [List.all_append]

theorem zip_all_false_at {α : Type} (Q : α × α → Bool) (l1 l2 : List α) (j : Nat) (x y : α)
    (h1 : l1[j]? = some x) (h2 : l2[j]? = some y) (hq : Q (x, y) = false) :
    (l1.zip l2).all Q = false :=
  List.all_eq_false.2 ⟨(x, y), List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨h1, h2⟩),
    by simp [hq]⟩

/-- A key-value's fields, read-only. -/
theorem KV_fields_disc (l : Loc) (v : KV) :
    (l ↦□ v : IProp GF) ⊢ l.[KV, go!"Key"] ↦□ v.Key' ∗ l.[KV, go!"R"] ↦□ v.R' := by
  iintro #H
  icases (AccessStrict.access_strict (A := l.[KV, go!"Key"] ↦□ v.Key')
      (A' := l.[KV, go!"Key"] ↦□ v.Key') (P := l ↦□ v)) $$ H with ⟨H1, -⟩
  icases (AccessStrict.access_strict (A := l.[KV, go!"R"] ↦□ v.R')
      (A' := l.[KV, go!"R"] ↦□ v.R') (P := l ↦□ v)) $$ H with ⟨H2, -⟩
  isplitl [H1]
  · iexact H1
  · iexact H2

/-- `outEqual`'s comparison of two key-values. -/
def QKV (p : KV × KV) : Bool := decide (p.1.Key' = p.2.Key' ∧ p.1.R' = p.2.R')

/-- `outEqual`'s comparison of two results. -/
def QRes (p : TRes × TRes) : Bool := resEqualL p.1 p.2

theorem outEqual.wp_proof (wp_vrEqual : vrEqual.spec (GF := GF) (hG := hG))
    (wp_resEqual : resEqual.spec (GF := GF) (hG := hG))
    (wp_kvsOf : kvsOf.spec (GF := GF) (hG := hG)) (wp_resOf : resOf.spec (GF := GF) (hG := hG)) :
    outEqual.spec (GF := GF) (hG := hG) := by
  intro kind a b
  wp_start
  wp_auto
  cases hae : a.Err'
  · try wp_auto
    cases hbe : b.Err'
    · try simp only [hbe]
      try wp_auto
      wp_if_destruct
      · have Hr := Hif; clear Hif
        wp_if_destruct
        · wp_if_destruct
          · have Hf := Hif; clear Hif
            cases haf : a.Found'
            · try simp only [haf]
              try wp_auto
              rw [show outEqualL (W64 0) a b = true by
                unfold outEqualL; rw [if_neg (by simp [hae, hbe, Hr]), if_pos rfl]; simp [← Hf, haf]]
              iapply HΦ; itrivial
            · try simp only [haf]
              try wp_auto
              wp_apply wp_vrEqual a.R' b.R'
              rw [show outEqualL (W64 0) a b = decide (a.R' = b.R') by
                unfold outEqualL; rw [if_neg (by simp [hae, hbe, Hr]), if_pos rfl]; simp [← Hf, haf]]
              iapply HΦ; itrivial
          · rw [show outEqualL (W64 0) a b = false by
              unfold outEqualL; rw [if_neg (by simp [hae, hbe, Hr]), if_pos rfl]; simp [Hif]]
            iapply HΦ; itrivial
        · have Hk0 := Hif; clear Hif
          wp_if_destruct
          · wp_if_destruct
            · have Hn := Hif; clear Hif
              wp_if_destruct
              · rw [show outEqualL (W64 1) a b = false by
                  unfold outEqualL
                  rw [if_neg (by simp [hae, hbe, Hr]), if_neg (by decide), if_pos rfl,
                    if_pos (Or.inr (by rw [show sint.Z (W64 3) = 3 by word] at Hif; exact Hif))]]
                iapply HΦ; itrivial
              · have Hn3 : ¬ 3 < sint.Z a.NKVs' := by rw [show sint.Z (W64 3) = 3 by word] at Hif; exact Hif
                clear Hif
                wp_apply wp_kvsOf a as %sa ⟨Hsa, -⟩
                wp_apply wp_kvsOf b as %sb ⟨Hsb, -⟩
                ipersist Hsa
                ipersist Hsb
                ihave %Hla := ownSlice_len $$ Hsa
                ihave %Hlb := ownSlice_len $$ Hsb
                have hval : outEqualL (W64 1) a b = ((kvsOfL a).zip (kvsOfL b)).all
                    QKV := by
                  unfold outEqualL
                  rw [if_neg (by simp [hae, hbe, Hr]), if_neg (by decide), if_pos rfl,
                    if_neg (by rintro (h | h); exact h Hn; exact Hn3 h)]
                  rfl
                rw [hval]
                rename_i iu_ptr
                irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
                have Hlen : sa.len = sb.len := by
                  have : (kvsOfL a).length = (kvsOfL b).length := by
                    unfold kvsOfL; rw [Hn]
                    by_cases h0 : 0 < sint.Z b.NKVs' <;> by_cases h1 : 1 < sint.Z b.NKVs' <;>
                      by_cases h2 : 2 < sint.Z b.NKVs' <;> simp [h0, h1, h2]
                  word
                ihave HI : (∃ (i j : w64),
                    "i" ∷ i_ptr ↦ i ∗ "Hiu" ∷ iu_ptr ↦ j ∗
                    "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sa.len ∧
                      (((kvsOfL a).take (sint.nat i)).zip ((kvsOfL b).take (sint.nat i))).all QKV =
                        true⌝ : IProp GF) $$ [i Hiu]
                · iexists W64 0, _
                  iframe
                  ipureintro; refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
                wp_for HI
                by_cases Hif : sint.Z i < sint.Z sa.len
                · (try simp only [decide_eq_true Hif, ↓reduceIte]); wp_pures; cleanup_bool_decide
                  (try wp_auto); cleanup_bool_decide
                  have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sa.len := ⟨Hi.1, Hif⟩
                  have Hb2' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sb.len := by rw [← Hlen]; exact Hb'
                  list_elem (kvsOfL a) (sint.nat i) as w
                  list_elem (kvsOfL b) (sint.nat i) as w2
                  ihave Hw := (ownSlice_elem_acc (sint.Z i) w sa DFrac.discard (kvsOfL a) Hi.1
                    Hw_lookup) $$ Hsa
                  icases Hw with ⟨#Hw, -⟩
                  ihave Hwf := KV_fields_disc _ w $$ Hw
                  icases Hwf with ⟨#Hwk, #Hwr⟩
                  ihave Hw2 := (ownSlice_elem_acc (sint.Z i) w2 sb DFrac.discard (kvsOfL b) Hi.1
                    Hw2_lookup) $$ Hsb
                  icases Hw2 with ⟨#Hw2, -⟩
                  ihave Hwf2 := KV_fields_disc _ w2 $$ Hw2
                  icases Hwf2 with ⟨#Hwk2, #Hwr2⟩
                  simp only [Hb', _root_.and_self, ↓reduceIte]
                  wp_apply wp_load_slice_index sa (sint.Z i) (kvsOfL a) _ w Hi.1 $$ [Hsa] as -
                  · isplit
                    · iexact Hsa
                    · ipureintro; exact Hw_lookup
                  simp only [Hb', _root_.and_self, ↓reduceIte]
                  wp_auto
                  simp only [Hb2', _root_.and_self, ↓reduceIte]
                  wp_auto
                  wp_if_destruct
                  · have Hk := Hif
                    simp only [Hb', _root_.and_self, ↓reduceIte]
                    wp_auto
                    simp only [Hb2', _root_.and_self, ↓reduceIte]
                    wp_auto
                    wp_apply wp_vrEqual w.R' w2.R'
                    wp_if_destruct
                    · wp_for_post
                      iframe
                      iexists i + W64 1, _
                      iframe
                      ipureintro
                      refine ⟨by word, by word, ?_⟩
                      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
                        zip_take_succ QKV _ _ _ w w2 Hw_lookup Hw2_lookup, Hi.2.2]
                      simp [QKV, Hk, Hif]
                    · wp_for_post
                      rw [zip_all_false_at QKV _ _ (sint.nat i) w w2 Hw_lookup Hw2_lookup
                        (by simp [QKV, Hif])]
                      iapply HΦ; itrivial
                  · wp_for_post
                    rw [zip_all_false_at QKV _ _ (sint.nat i) w w2 Hw_lookup Hw2_lookup
                      (by simp [QKV, Hif])]
                    iapply HΦ; itrivial
                · (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]); wp_pures
                  cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
                  have e1 : (kvsOfL a).take (sint.nat i) = kvsOfL a := List.take_of_length_le (by word)
                  have e2 : (kvsOfL b).take (sint.nat i) = kvsOfL b :=
                    List.take_of_length_le (by rw [Hlb.1, ← Hlen]; word)
                  have := Hi.2.2
                  rw [e1, e2] at this
                  rw [this]
                  iapply HΦ; itrivial
            · rw [show outEqualL (W64 1) a b = false by
                unfold outEqualL
                rw [if_neg (by simp [hae, hbe, Hr]), if_neg (by decide), if_pos rfl,
                  if_pos (Or.inl Hif)]]
              iapply HΦ; itrivial
          · have Hk1 := Hif; clear Hif
            wp_if_destruct
            · rw [show outEqualL (W64 2) a b = true by
                unfold outEqualL
                rw [if_neg (by simp [hae, hbe, Hr]), if_neg (by decide), if_neg (by decide),
                  if_pos rfl]]
              iapply HΦ; itrivial
            · have Hk2 := Hif; clear Hif
              wp_if_destruct
              · rw [show outEqualL (W64 3) a b = decide (a.N' = b.N') by
                  unfold outEqualL
                  rw [if_neg (by simp [hae, hbe, Hr]), if_neg (by decide), if_neg (by decide),
                    if_neg (by decide), if_pos rfl]]
                iapply HΦ; itrivial
              · have Hk3 := Hif; clear Hif
                have hpre : ∀ (c : Prop) [Decidable c] (u v : Bool),
                    outEqualL kind a b = (if c then u else v) → True := fun _ _ _ _ _ => trivial
                clear hpre
                wp_if_destruct
                · have Ho := Hif; clear Hif
                  wp_if_destruct
                  · have Hn := Hif; clear Hif
                    wp_if_destruct
                    · rw [show outEqualL kind a b = false by
                        unfold outEqualL
                        rw [if_neg (by simp [hae, hbe, Hr]), if_neg Hk0, if_neg Hk1, if_neg Hk2,
                          if_neg Hk3, if_pos (Or.inr (Or.inr (by rw [show sint.Z (W64 3) = 3 by word] at Hif; exact Hif)))]]
                      iapply HΦ; itrivial
                    · have Hn3 : ¬ 3 < sint.Z a.NRes' := by rw [show sint.Z (W64 3) = 3 by word] at Hif; exact Hif
                      clear Hif
                      wp_apply wp_resOf a as %sa ⟨Hsa, -⟩
                      wp_apply wp_resOf b as %sb ⟨Hsb, -⟩
                      ipersist Hsa
                      ipersist Hsb
                      ihave %Hla := ownSlice_len $$ Hsa
                      ihave %Hlb := ownSlice_len $$ Hsb
                      have hval : outEqualL kind a b = ((resOfL a).zip (resOfL b)).all QRes := by
                        unfold outEqualL
                        rw [if_neg (by simp [hae, hbe, Hr]), if_neg Hk0, if_neg Hk1, if_neg Hk2,
                          if_neg Hk3, if_neg (by rintro (h | h | h); exact h Ho; exact h Hn; exact Hn3 h)]
                        rfl
                      rw [hval]
                      rename_i iu_ptr
                      irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
                      have Hlen : sa.len = sb.len := by
                        have : (resOfL a).length = (resOfL b).length := by
                          unfold resOfL; rw [Hn]
                          by_cases h0 : 0 < sint.Z b.NRes' <;> by_cases h1 : 1 < sint.Z b.NRes' <;>
                            by_cases h2 : 2 < sint.Z b.NRes' <;> simp [h0, h1, h2]
                        word
                      ihave HI : (∃ (i j : w64),
                          "i" ∷ i_ptr ↦ i ∗ "Hiu" ∷ iu_ptr ↦ j ∗
                          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sa.len ∧
                            (((resOfL a).take (sint.nat i)).zip ((resOfL b).take (sint.nat i))).all
                              QRes = true⌝ : IProp GF) $$ [i Hiu]
                      · iexists W64 0, _
                        iframe
                        ipureintro; refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
                      wp_for HI
                      by_cases Hif : sint.Z i < sint.Z sa.len
                      · (try simp only [decide_eq_true Hif, ↓reduceIte]); wp_pures; cleanup_bool_decide
                        (try wp_auto); cleanup_bool_decide
                        have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sa.len := ⟨Hi.1, Hif⟩
                        have Hb2' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sb.len := by
                          rw [← Hlen]; exact Hb'
                        list_elem (resOfL a) (sint.nat i) as w
                        list_elem (resOfL b) (sint.nat i) as w2
                        simp only [Hb', _root_.and_self, ↓reduceIte]
                        wp_apply wp_load_slice_index sa (sint.Z i) (resOfL a) _ w Hi.1 $$ [Hsa] as -
                        · isplit
                          · iexact Hsa
                          · ipureintro; exact Hw_lookup
                        simp only [Hb', _root_.and_self, ↓reduceIte]
                        wp_apply wp_load_slice_index sa (sint.Z i) (resOfL a) _ w Hi.1 $$ [Hsa] as -
                        · isplit
                          · iexact Hsa
                          · ipureintro; exact Hw_lookup
                        simp only [Hb2', _root_.and_self, ↓reduceIte]
                        wp_apply wp_load_slice_index sb (sint.Z i) (resOfL b) _ w2 Hi.1 $$ [Hsb] as -
                        · isplit
                          · iexact Hsb
                          · ipureintro; exact Hw2_lookup
                        wp_apply wp_resEqual w w2
                        cases hq : resEqualL w w2
                        · try wp_auto
                          wp_for_post
                          rw [zip_all_false_at QRes _ _ (sint.nat i) w w2 Hw_lookup Hw2_lookup
                            (by simp [QRes, hq])]
                          iapply HΦ; itrivial
                        · try wp_auto
                          wp_for_post
                          iframe
                          iexists i + W64 1, _
                          iframe
                          ipureintro
                          refine ⟨by word, by word, ?_⟩
                          rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
                            zip_take_succ QRes _ _ _ w w2 Hw_lookup Hw2_lookup, Hi.2.2]
                          simp [QRes, hq]
                      · (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]); wp_pures
                        cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
                        have e1 : (resOfL a).take (sint.nat i) = resOfL a :=
                          List.take_of_length_le (by word)
                        have e2 : (resOfL b).take (sint.nat i) = resOfL b :=
                          List.take_of_length_le (by rw [Hlb.1, ← Hlen]; word)
                        have := Hi.2.2
                        rw [e1, e2] at this
                        rw [this]
                        iapply HΦ; itrivial
                  · rw [show outEqualL kind a b = false by
                      unfold outEqualL
                      rw [if_neg (by simp [hae, hbe, Hr]), if_neg Hk0, if_neg Hk1, if_neg Hk2,
                        if_neg Hk3, if_pos (Or.inr (Or.inl Hif))]]
                    iapply HΦ; itrivial
                · rw [show outEqualL kind a b = false by
                    unfold outEqualL
                    rw [if_neg (by simp [hae, hbe, Hr]), if_neg Hk0, if_neg Hk1, if_neg Hk2,
                      if_neg Hk3, if_pos (Or.inl Hif)]]
                  iapply HΦ; itrivial
      · rw [show outEqualL kind a b = false by
          unfold outEqualL; rw [if_pos (by simp [hae, hbe, Hif])]]
        iapply HΦ; itrivial
    · try simp only [hbe]
      try wp_auto
      rw [show outEqualL kind a b = false by unfold outEqualL; rw [if_pos (by simp [hbe])]]
      iapply HΦ; itrivial
  · try wp_auto
    rw [show outEqualL kind a b = false by unfold outEqualL; rw [if_pos (by simp [hae])]]
    iapply HΦ; itrivial

end proof

end linkvtxn
end EtcdGrove
end Perennial
