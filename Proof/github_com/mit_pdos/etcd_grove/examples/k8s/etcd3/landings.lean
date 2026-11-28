module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.landings
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.shows
public import Perennial.Spec.sort.Search

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (mstore mcfg Input Output Revs)

section pure
variable [GooseExts]

/-- `dropWhile` drops the prefix where the test holds. -/
theorem dropWhile_eq_drop {α : Type} (p : α → Bool) : ∀ (L : List α) (i : Nat), i ≤ L.length →
    (∀ k (hk : k < L.length), k < i → p L[k] = true) → (∀ hi : i < L.length, p L[i] = false) →
    L.dropWhile p = L.drop i := by
  intro L
  induction L with
  | nil => intro i _ _ _; simp
  | cons a L ih =>
    intro i hi h1 h2
    cases i with
    | zero =>
      have : p a = false := h2 (by simp)
      simp [this]
    | succ i =>
      have ha : p a = true := h1 0 (by simp) (by omega)
      simp only [List.dropWhile_cons, ha, ↓reduceIte, List.drop_succ_cons]
      exact ih i (by simp at hi; omega) (fun k hk hki => h1 (k + 1) (by simp; omega) (by omega))
        (fun hi' => h2 (by simp; omega))

/-- `sort.Search`'s test over the anchors: the `i`-th is at least `rv`. -/
def ancF (A : List w64) (rv : w64) : Int → Bool :=
  fun i => decide (uint.nat rv ≤ uint.nat (A.getD i.toNat (W64 0)))

theorem uintZ_le_iff (a b : w64) : uint.Z a ≤ uint.Z b ↔ uint.nat a ≤ uint.nat b := by
  constructor <;> intro h <;> word

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem keyRevs_get (M : GMap GoString GoSlice) (F : GoString → List w64) (k : GoString)
    (hn : ∀ k, M !! k = none → F k = []) :
    ([∗map] k ↦ sl ∈ M, sl ↦*□ F k) ⊢ ((M !! k).getD (zero_val GoSlice) ↦*□ F k : IProp GF) := by
  cases h : M !! k with
  | none =>
    rw [hn k h, Option.getD_none, show zero_val GoSlice = slice.nil from rfl]
    iintro _
    iapply (ownSlice_nil (V := w64) DFrac.discard)
  | some sl =>
    exact BigSepM.bigSepM_lookup (Φ := fun k (sl : GoSlice) => (sl ↦*□ F k : IProp GF)) h

theorem landings.wp_proof
    (wp_shows : shows.spec (GF := GF) (hG := hG))
    (wp_Search : sort.Search.spec (GF := GF) (hG := hG)) :
    landings.spec (GF := GF) (hG := hG) := fun r R c w b full x y => by
  wp_start as #Hr
  unfold revsOwn
  icases Hr with ⟨#Ha, %Hsorted, #Hbk, #Hfk⟩
  wp_auto
  wp_apply wp_slice_literal (V := w64) (l := [c.st'.rv' + W64 1])
  isplitr
  · ipureintro; rfl
  iintro %lsl0 ⟨Hls, Hlscap⟩
  wp_auto
  irename : (in_ptr ↦ x : IProp GF) => Hin
  ipersist full
  ipersist b
  ipersist next
  wp_pures
  generalize hf : (func.mk BAnon (BNamed "r") _ : GoFunc) = f at *
  ipersist add
  ihave #Hadd : iprop(∀ (rr : w64) (L : List w64) (sl : GoSlice),
      {{ in_ptr ↦ x ∗ out_ptr ↦ y ∗ w_ptr ↦ w ∗
          ls_ptr ↦ sl ∗ sl ↦* L ∗ ownSliceCap w64 sl (DFrac.own 1) }}
        (App (Val #f) (Val #rr))
      {{ RET #(); ∃ sl' : GoSlice, in_ptr ↦ x ∗ out_ptr ↦ y ∗ w_ptr ↦ w ∗ ls_ptr ↦ sl' ∗
          sl' ↦* (L ++ [rr].filter (landOkL c.st'.rv' w b full x y)) ∗
          ownSliceCap w64 sl' (DFrac.own 1) }}) $$ []
  · iintro %rr %L %sl !> %Φ' ⟨Hin, Hout, Hw, Hl, Hsl, Hcap⟩ HΦ'
    rw [← hf, ← recv_eq_func_mk]
    have Hgt : uint.Z (c.st'.rv' + W64 1) < uint.Z rr → uint.nat (c.st'.rv' + W64 1) < uint.nat rr :=
      fun h => by word
    have Hn : ¬ uint.Z (c.st'.rv' + W64 1) < uint.Z rr → ¬ uint.nat (c.st'.rv' + W64 1) < uint.nat rr :=
      fun h => by word
    have Hb0 : uint.Z (W64 0) < uint.Z b → b ≠ W64 0 := fun h h0 => by subst h0; word
    have Hbz : ¬ uint.Z (W64 0) < uint.Z b → b = W64 0 := fun h => by word
    have Hrb : uint.Z rr ≤ uint.Z b → uint.nat rr ≤ uint.nat b := fun h => by word
    have Hnrb : ¬ uint.Z rr ≤ uint.Z b → ¬ uint.nat rr ≤ uint.nat b := fun h => by word
    wp_auto
    wp_if_destruct
    · have hgt := Hgt Hif
      wp_if_destruct
      · wp_if_destruct
        · have hb0 := Hb0 Hif
          wp_if_destruct
          · have hok : landOkL c.st'.rv' w b false x y rr = true := by
              have hrb := Hrb Hif
              unfold landOkL; rw [decide_eq_true hgt]; simp [hrb]; exact Or.inl hb0
            wp_pures
            (try wp_auto)
            wp_apply wp_slice_literal (V := w64) (l := [rr])
            isplitr
            · ipureintro; rfl
            iintro %ls1 ⟨Hl1, _⟩
            wp_apply wp_slice_append $$ [$Hsl $Hcap $Hl1] as %sl' ⟨Hsl', Hcap', -⟩
            iapply HΦ'
            iexists sl'
            simp only [List.filter_cons, List.filter_nil, hok, ↓reduceIte]
            iframe
          · have hnb : (decide (b ≠ W64 0) && decide (uint.nat rr ≤ uint.nat b)) = false := by
              have hrb := Hnrb Hif
              simp [hrb]
            wp_apply wp_shows
            cases hs : showsL x y w.Key' rr
            · have hok : landOkL c.st'.rv' w b false x y rr = false := by
                simp only [landOkL, hnb, hs, Bool.or_false, Bool.and_false]
              wp_pures
              iapply HΦ'
              iexists sl
              simp only [List.filter_cons, List.filter_nil, hok, Bool.false_eq_true, ↓reduceIte, List.append_nil]
              iframe
            · have hok : landOkL c.st'.rv' w b false x y rr = true := by
                unfold landOkL; rw [decide_eq_true hgt]; simp [hs]
              wp_pures
              (try wp_auto)
              wp_apply wp_slice_literal (V := w64) (l := [rr])
              isplitr
              · ipureintro; rfl
              iintro %ls1 ⟨Hl1, _⟩
              wp_apply wp_slice_append $$ [$Hsl $Hcap $Hl1] as %sl' ⟨Hsl', Hcap', -⟩
              iapply HΦ'
              iexists sl'
              simp only [List.filter_cons, List.filter_nil, hok, ↓reduceIte]
              iframe
        · have hnb : (decide (b ≠ W64 0) && decide (uint.nat rr ≤ uint.nat b)) = false := by
            have hb0 := Hbz Hif
            simp [hb0]
          wp_apply wp_shows
          cases hs : showsL x y w.Key' rr
          · have hok : landOkL c.st'.rv' w b false x y rr = false := by
              simp only [landOkL, hnb, hs, Bool.or_false, Bool.and_false]
            wp_pures
            iapply HΦ'
            iexists sl
            simp only [List.filter_cons, List.filter_nil, hok, Bool.false_eq_true, ↓reduceIte, List.append_nil]
            iframe
          · have hok : landOkL c.st'.rv' w b false x y rr = true := by
              unfold landOkL; rw [decide_eq_true hgt]; simp [hs]
            wp_pures
            (try wp_auto)
            wp_apply wp_slice_literal (V := w64) (l := [rr])
            isplitr
            · ipureintro; rfl
            iintro %ls1 ⟨Hl1, _⟩
            wp_apply wp_slice_append $$ [$Hsl $Hcap $Hl1] as %sl' ⟨Hsl', Hcap', -⟩
            iapply HΦ'
            iexists sl'
            simp only [List.filter_cons, List.filter_nil, hok, ↓reduceIte]
            iframe
      · have hok : landOkL c.st'.rv' w b true x y rr = true := by
          simp only [landOkL, Bool.true_or, Bool.and_true, decide_eq_true_eq]; exact hgt
        wp_pures
        wp_apply wp_slice_literal (V := w64) (l := [rr])
        isplitr
        · ipureintro; rfl
        iintro %ls1 ⟨Hl1, _⟩
        wp_apply wp_slice_append $$ [$Hsl $Hcap $Hl1] as %sl' ⟨Hsl', Hcap', -⟩
        iapply HΦ'
        iexists sl'
        simp only [List.filter_cons, List.filter_nil, hok, ↓reduceIte]
        iframe
    · have hn := Hn Hif
      have hok : landOkL c.st'.rv' w b full x y rr = false := by
        simp only [landOkL, decide_eq_false hn, Bool.false_and]
      iapply HΦ'
      iexists sl
      simp only [List.filter_cons, List.filter_nil, hok, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      iframe
  cases full <;> wp_pures <;> (try wp_auto)
  all_goals
    iunfold keyRevsOwn at Hbk Hfk
    icases Hbk with ⟨%Mb, #Hbm, %Hbnone, #Hbs⟩
    icases Hfk with ⟨%Mf, #Hfm, %Hfnone, #Hfs⟩
  · wp_apply (wp_map_lookup1 (K := GoString) (V := GoSlice) go.string _ r.fastByKey' Mf w.Key' DFrac.discard) $$ Hfm as -
    ihave #Hsk := keyRevs_get Mf R.fastByKey w.Key' Hfnone $$ Hfs
    generalize (Mf !! w.Key').getD (zero_val GoSlice) = sk at *
    ihave %Hskl := ownSlice_len $$ Hsk
    ihave HL : (∃ (j rv' : w64) (sl : GoSlice),
        "i" ∷ i_ptr ↦ j ∗ "r" ∷ r_ptr ↦ rv' ∗ "ls" ∷ ls_ptr ↦ sl ∗
        "Hls" ∷ sl ↦* ([c.st'.rv' + W64 1] ++
          (((R.fastByKey w.Key').take (sint.nat j)).filter (landOkL c.st'.rv' w b false x y))) ∗
        "Hlscap" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sk.len⌝ : IProp GF) $$ [i r ls Hls Hlscap]
    · iexists W64 0, _, _
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil, List.append_nil]
      iframe
      ipureintro; word
    wp_for HL
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sk.len := ⟨Hj.1, by simpa using Hif⟩
      have hjl : sint.nat j < (R.fastByKey w.Key').length := by word
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      simp only [Hb', _root_.and_self, ↓reduceIte]
      list_elem (R.fastByKey w.Key') (sint.nat j) as kv
      wp_apply wp_load_slice_index sk (sint.Z j) _ DFrac.discard kv Hj.1 $$ [Hsk] as Hjunk
      · isplit
        · iexact Hsk
        · ipureintro; exact Hkv_lookup
      iclear Hjunk
      wp_apply Hadd $$ [$Hin $out $w $ls $Hls $Hlscap] as ⟨%sl', Hin, out, w, ls, Hls, Hlscap⟩
      wp_for_post
      iframe
      iexists j + W64 1, kv, sl'
      rw [hj1, List.take_add_one, Hkv_lookup, Option.toList_some, List.filter_append, List.append_assoc]
      iframe
      ipureintro; word
    · have hjk : sint.nat j = (R.fastByKey w.Key').length := by word
      rw [hjk, List.take_length]
      have HL1 : ¬(x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5) →
          landingsL R c.st'.rv' w b false x y = [c.st'.rv' + W64 1] ++
            (R.fastByKey w.Key').filter (landOkL c.st'.rv' w b false x y) := by
        intro h; simp only [landingsL, if_neg h, Bool.false_eq_true, ↓reduceIte]
      have HL2 : (x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5) →
          landingsL R c.st'.rv' w b false x y = [c.st'.rv' + W64 1] ++
            (R.fastByKey w.Key').filter (landOkL c.st'.rv' w b false x y) ++
            [y.RV'].filter (landOkL c.st'.rv' w b false x y) := by
        intro h; simp only [landingsL, if_pos h, Bool.false_eq_true, ↓reduceIte]
      wp_if_destruct
      · have h1 := Hif
        wp_if_destruct
        · have h2 := Hif
          wp_if_destruct
          · have h3 := Hif
            (try wp_auto)
            iapply HΦ
            rw [HL1 (fun h => h.2.2.1 h3)]
            iframe
          · have h3 := Hif
            wp_if_destruct
            · have h4 := Hif
              (try wp_auto)
              iapply HΦ
              rw [HL1 (fun h => h.2.2.2 h4)]
              iframe
            · have h4 := Hif
              wp_apply Hadd $$ [$Hin $out $w $ls $Hls $Hlscap] as ⟨%sl', Hin, out, w, ls, Hls, Hlscap⟩
              (try wp_auto)
              iapply HΦ
              rw [HL2 ⟨h1, h2, h3, h4⟩]
              iframe
        · have h2 := Hif
          (try wp_auto)
          iapply HΦ
          rw [HL1 (fun h => h2 h.2.1)]
          iframe
      · have h1 := Hif
        (try wp_auto)
        iapply HΦ
        rw [HL1 (fun h => h1 h.1)]
        iframe
  · wp_apply (wp_map_lookup1 (K := GoString) (V := GoSlice) go.string _ r.byKey' Mb w.Key' DFrac.discard) $$ Hbm as -
    ihave #Hsk := keyRevs_get Mb R.byKey w.Key' Hbnone $$ Hbs
    generalize (Mb !! w.Key').getD (zero_val GoSlice) = sk at *
    ihave %Hskl := ownSlice_len $$ Hsk
    ihave HL : (∃ (j rv' : w64) (sl : GoSlice),
        "i" ∷ i_ptr ↦ j ∗ "r" ∷ r_ptr ↦ rv' ∗ "ls" ∷ ls_ptr ↦ sl ∗
        "Hls" ∷ sl ↦* ([c.st'.rv' + W64 1] ++
          (((R.byKey w.Key').take (sint.nat j)).filter (landOkL c.st'.rv' w b true x y))) ∗
        "Hlscap" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sk.len⌝ : IProp GF) $$ [i r ls Hls Hlscap]
    · iexists W64 0, _, _
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil, List.append_nil]
      iframe
      ipureintro; word
    wp_for HL
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sk.len := ⟨Hj.1, by simpa using Hif⟩
      have hjl : sint.nat j < (R.byKey w.Key').length := by word
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      simp only [Hb', _root_.and_self, ↓reduceIte]
      list_elem (R.byKey w.Key') (sint.nat j) as kv
      wp_apply wp_load_slice_index sk (sint.Z j) _ DFrac.discard kv Hj.1 $$ [Hsk] as Hjunk
      · isplit
        · iexact Hsk
        · ipureintro; exact Hkv_lookup
      iclear Hjunk
      wp_apply Hadd $$ [$Hin $out $w $ls $Hls $Hlscap] as ⟨%sl', Hin, out, w, ls, Hls, Hlscap⟩
      wp_for_post
      iframe
      iexists j + W64 1, kv, sl'
      rw [hj1, List.take_add_one, Hkv_lookup, Option.toList_some, List.filter_append, List.append_assoc]
      iframe
      ipureintro; word
    · have hjk : sint.nat j = (R.byKey w.Key').length := by word
      rw [hjk, List.take_length]
      wp_bind (If _ _ _)
      iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ sl' : GoSlice, in_ptr ↦ x ∗ out_ptr ↦ y ∗
          w_ptr ↦ w ∗ ls_ptr ↦ sl' ∗
          sl' ↦* (if (x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5) then ([c.st'.rv' + W64 1] ++ (R.byKey w.Key').filter (landOkL c.st'.rv' w b true x y)) ++ [y.RV'].filter (landOkL c.st'.rv' w b true x y) else ([c.st'.rv' + W64 1] ++ (R.byKey w.Key').filter (landOkL c.st'.rv' w b true x y))) ∗
          ownSliceCap w64 sl' (DFrac.own 1))) $$ [Hin out w ls Hls Hlscap]
      · wp_if_destruct
        · have h1 := Hif
          wp_if_destruct
          · have h2 := Hif
            wp_if_destruct
            · have h3 := Hif
              (try wp_auto)
              isplitr
              · ipureintro; first | rfl | trivial
              iexists _
              rw [if_neg (fun h : (x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5) => h.2.2.1 h3)]
              iframe
            · have h3 := Hif
              wp_if_destruct
              · have h4 := Hif
                (try wp_auto)
                isplitr
                · ipureintro; first | rfl | trivial
                iexists _
                rw [if_neg (fun h : (x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5) => h.2.2.2 h4)]
                iframe
              · have h4 := Hif
                wp_apply Hadd $$ [$Hin $out $w $ls $Hls $Hlscap] as ⟨%sl', Hin, out, w, ls, Hls, Hlscap⟩
                (try wp_auto)
                isplitr
                · ipureintro; first | rfl | trivial
                iexists _
                rw [if_pos (⟨h1, h2, h3, h4⟩ : (x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5))]
                iframe
          · have h2 := Hif
            (try wp_auto)
            isplitr
            · ipureintro; first | rfl | trivial
            iexists _
            rw [if_neg (fun h : (x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5) => h2 h.2.1)]
            iframe
        · have h1 := Hif
          (try wp_auto)
          isplitr
          · ipureintro; first | rfl | trivial
          iexists _
          rw [if_neg (fun h : (x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5) => h1 h.1)]
          iframe
      iintro %v ⟨%hv, %sl', Hin, out, w, ls, Hls, Hlscap⟩
      subst hv
      wp_auto
      ihave %Hal := ownSlice_len $$ Ha
      have Hmono : sort.IsMonoPred (ancF R.anchors c.st'.rv') (sint.Z r.anchors'.len) := by
        intro i j hij hfi
        simp only [ancF, decide_eq_true_eq] at hfi ⊢
        have hj : j.toNat < R.anchors.length := by word
        have hi : i.toNat < j.toNat := by omega
        have hi' : i.toNat < R.anchors.length := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
          List.getElem?_eq_getElem hi', Option.getD_some] at hfi ⊢
        have := List.pairwise_iff_getElem.1 Hsorted i.toNat j.toNat hi' hj hi
        omega
      rw [show ∀ x b, (RecV BAnon x b : val) = #(func.mk BAnon x b) from
        fun x b => by rw [go.intoVal_unfold GoFunc]]
      wp_apply wp_Search _ _ (ancF R.anchors c.st'.rv') iprop(revs_ptr ↦ r ∗ c_ptr ↦ c) $$ [revs c]
      · iframe
        isplitr
        · ipureintro; exact Hal.2
        isplitr
        · unfold sort.predImplements
          iintro %i
          wp_start as ⟨⟨Hrevs, Hc⟩, %Hbound⟩
          wp_auto
          simp only [Hbound.1, Hbound.2, _root_.and_self, ↓reduceIte]
          have hil : sint.nat i < R.anchors.length := by word
          list_elem R.anchors (sint.nat i) as ai
          wp_apply wp_load_slice_index r.anchors' (sint.Z i) R.anchors DFrac.discard ai Hbound.1 $$ [Ha] as Hjunk
          · isplit
            · iexact Ha
            · ipureintro; exact Hai_lookup
          iclear Hjunk
          iapply HΦ
          iframe
          ipureintro
          simp only [ancF, show (sint.Z i).toNat = sint.nat i from rfl, List.getD_eq_getElem?_getD,
            Hai_lookup, Option.getD_some]
          exact decide_eq_decide.2 (uintZ_le_iff _ _)
        ipureintro; exact Hmono
      iintro %i0 ⟨⟨revs, c⟩, %Hi0, %Hfound, %Hoob, %Hlt⟩
      wp_auto
      have Hi0n : sint.Z i0 ≤ sint.Z r.anchors'.len := Classical.byContradiction fun hc => by
        have := Hoob (fun k hk => Hlt k ⟨hk.1, by omega⟩)
        omega
      have Hdrop : R.anchors.dropWhile (fun a => decide (uint.nat a < uint.nat c.st'.rv')) =
          R.anchors.drop (sint.nat i0) := by
        apply dropWhile_eq_drop _ _ _ (by word)
        · intro k hk hki
          have := Hlt k ⟨by omega, by word⟩
          simp only [ancF, show (k : Int).toNat = k from rfl, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hk, Option.getD_some, decide_eq_false_iff_not] at this
          simp only [decide_eq_true_eq]; omega
        · intro hi
          have := Hfound (by word)
          simp only [ancF, show (sint.Z i0).toNat = sint.nat i0 from rfl, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hi, Option.getD_some, decide_eq_true_eq] at this
          simp only [decide_eq_false_iff_not]; omega
      have HLand : landingsL R c.st'.rv' w b true x y = (if (x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5) then ([c.st'.rv' + W64 1] ++ (R.byKey w.Key').filter (landOkL c.st'.rv' w b true x y)) ++ [y.RV'].filter (landOkL c.st'.rv' w b true x y) else ([c.st'.rv' + W64 1] ++ (R.byKey w.Key').filter (landOkL c.st'.rv' w b true x y))) ++
          ((R.anchors.drop (sint.nat i0)).flatMap (fun a => [a, a + W64 1])).filter (landOkL c.st'.rv' w b true x y) := by
        rw [← Hdrop]; rfl
      ihave HA : (∃ (k : w64) (sl : GoSlice),
          "i" ∷ i_ptr ↦ k ∗ "ls" ∷ ls_ptr ↦ sl ∗
          "Hls" ∷ sl ↦* ((if (x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5) then ([c.st'.rv' + W64 1] ++ (R.byKey w.Key').filter (landOkL c.st'.rv' w b true x y)) ++ [y.RV'].filter (landOkL c.st'.rv' w b true x y) else ([c.st'.rv' + W64 1] ++ (R.byKey w.Key').filter (landOkL c.st'.rv' w b true x y))) ++ (((R.anchors.drop (sint.nat i0)).take (sint.nat k - sint.nat i0)).flatMap
            (fun a => [a, a + W64 1])).filter (landOkL c.st'.rv' w b true x y)) ∗
          "Hlscap" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗
          "%Hk" ∷ ⌜sint.Z i0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z r.anchors'.len⌝ : IProp GF) $$ [i ls Hls Hlscap]
      · iexists i0, sl'
        rw [Nat.sub_self, List.take_zero, List.flatMap_nil, List.filter_nil, List.append_nil]
        iframe
        ipureintro; omega
      wp_for HA
      wp_if_destruct
      · have Hkb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z r.anchors'.len := ⟨by omega, by simpa using Hif⟩
        have hkl : sint.nat k < R.anchors.length := by word
        have hk1 : sint.nat (k + W64 1) - sint.nat i0 = (sint.nat k - sint.nat i0) + 1 := by word
        have hki : sint.nat i0 + (sint.nat k - sint.nat i0) = sint.nat k := by word
        simp only [Hkb, _root_.and_self, ↓reduceIte]
        list_elem R.anchors (sint.nat k) as ak
        wp_apply wp_load_slice_index r.anchors' (sint.Z k) R.anchors DFrac.discard ak Hkb.1 $$ [Ha] as Hjunk
        · isplit
          · iexact Ha
          · ipureintro; exact Hak_lookup
        iclear Hjunk
        wp_apply Hadd $$ [$Hin $out $w $ls $Hls $Hlscap] as ⟨%sl1, Hin, out, w, ls, Hls, Hlscap⟩
        simp only [Hkb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index r.anchors' (sint.Z k) R.anchors DFrac.discard ak Hkb.1 $$ [Ha] as Hjunk
        · isplit
          · iexact Ha
          · ipureintro; exact Hak_lookup
        iclear Hjunk
        wp_apply Hadd $$ [$Hin $out $w $ls $Hls $Hlscap] as ⟨%sl2, Hin, out, w, ls, Hls, Hlscap⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists k + W64 1, sl2
        have hd : (R.anchors.drop (sint.nat i0))[sint.nat k - sint.nat i0]? = some ak := by
          rw [List.getElem?_drop, hki, Hak_lookup]
        rw [hk1, List.take_add_one, hd, Option.toList_some, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, show [ak, ak + W64 1] = [ak] ++ [ak + W64 1] from rfl,
          List.filter_append, List.filter_append]
        simp only [List.append_assoc]
        iframe
        ipureintro; word
      · have hkn : sint.nat k - sint.nat i0 = (R.anchors.drop (sint.nat i0)).length := by
          rw [List.length_drop]; word
        rw [hkn, List.take_length]
        iapply HΦ
        rw [HLand]
        iframe

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
