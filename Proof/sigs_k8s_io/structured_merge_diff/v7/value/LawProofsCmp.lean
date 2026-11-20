/-
**Helpers of `value`'s comparison/equality recursion** (structured-merge-diff v7.0.0): a list
view's `RangeUsing` from the concrete specs of its two dynamic types (for `ListCompareUsing`, which
does not call `Length`), and the pure facts of `MapCompareUsing`'s zip in lexical order. Defs-tier: imports specs, never proofs. Prove phase (2026-11-20).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsCompare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing_ptr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

/-! ## `MapCompareUsing`'s zip in lexical order -/

namespace ValueCmp

open ValuePure ValueCompare

theorem zipLexical_fuel : ∀ (n m : Nat) (xs ys : List (GoString × UVal)),
    xs.length + ys.length < n → xs.length + ys.length < m →
    zipLexical n xs ys = zipLexical m xs ys
  | 0, _, _, _, h, _ => by omega
  | _, 0, _, _, _, h => by omega
  | n + 1, m + 1, [], [], _, _ => by simp [zipLexical]
  | n + 1, m + 1, (_, _) :: _, [], _, _ => by simp [zipLexical]
  | n + 1, m + 1, [], (_, _) :: _, _, _ => by simp [zipLexical]
  | n + 1, m + 1, (k, a) :: xs, (k', b) :: ys, h1, h2 => by
    simp only [zipLexical]
    simp only [List.length_cons] at h1 h2
    rw [zipLexical_fuel n m xs ys (by omega) (by omega),
      zipLexical_fuel n m xs ((k', b) :: ys) (by simp; omega) (by simp; omega),
      zipLexical_fuel n m ((k, a) :: xs) ys (by simp; omega) (by simp; omega)]

/-- The zip with enough fuel. -/
def zl (xs ys : List (GoString × UVal)) : List (GoString × Option UVal × Option UVal) :=
  zipLexical (xs.length + ys.length + 1) xs ys

theorem zipKeys_zl (ol or_ : Option (List (GoString × UVal))) :
    zipKeys ol or_ = (zl (kvsOrEmpty ol) (kvsOrEmpty or_)).map (·.1) := rfl

theorem zl_cons_same (k : GoString) (a b : UVal) (xs ys : List (GoString × UVal)) :
    zl ((k, a) :: xs) ((k, b) :: ys) = (k, some a, some b) :: zl xs ys := by
  unfold zl
  simp only [List.length_cons]
  rw [show xs.length + 1 + (ys.length + 1) + 1 = (xs.length + ys.length + 2) + 1 by omega]
  simp only [zipLexical, ↓reduceIte]
  rw [zipLexical_fuel (xs.length + ys.length + 2) (xs.length + ys.length + 1) xs ys (by omega) (by omega)]

theorem zl_prefix : ∀ (p xs ys : List (GoString × UVal)),
    zl (p ++ xs) (p ++ ys) = p.map (fun e => (e.1, some e.2, some e.2)) ++ zl xs ys
  | [], _, _ => rfl
  | (k, a) :: p, xs, ys => by
    simp only [List.cons_append, zl_cons_same, zl_prefix p xs ys, List.map_cons]

theorem zl_nil_nil : zl [] [] = [] := by simp [zl, zipLexical]

theorem zl_ne_nil {xs ys : List (GoString × UVal)} (h : zl xs ys = []) : xs = [] ∧ ys = [] := by
  unfold zl at h
  match xs, ys with
  | [], [] => exact ⟨rfl, rfl⟩
  | (_, _) :: _, [] => simp [zipLexical] at h
  | [], (_, _) :: _ => simp [zipLexical] at h
  | (k, _) :: _, (k', _) :: _ =>
    simp only [List.length_cons, zipLexical] at h
    by_cases e : k = k' <;> by_cases l : gsLt k k' = true <;> simp [e, l] at h

theorem listCmp_prefix {α : Type} (f : α → α → Int) (hf : ∀ x, f x x = 0) :
    ∀ (p xs ys : List α), listCmp f (p ++ xs) (p ++ ys) = listCmp f xs ys
  | [], _, _ => rfl
  | x :: p, xs, ys => by simp only [List.cons_append, listCmp, hf, ↓reduceIte, listCmp_prefix f hf p]

theorem pairCmp_self (p : GoString × UVal) : pairCmp UVal.compare p p = 0 := by
  simp [pairCmp, gsCompare_self, compare_self]

theorem keysSorted_append_right {α : Type} : ∀ (p xs : List (GoString × α)),
    keysSorted (p ++ xs) = true → keysSorted xs = true
  | [], _, h => h
  | (k, v) :: p, xs, h => keysSorted_append_right p xs (keysSorted_tail h)

theorem lookupKV_append_notin {α : Type} {k : GoString} : ∀ (p xs : List (GoString × α)),
    k ∉ kvKeys p → lookupKV k (p ++ xs) = lookupKV k xs
  | [], _, _ => rfl
  | (k', v) :: p, xs, h => by
    simp only [kvKeys, List.map_cons, List.mem_cons, not_or] at h
    simp only [List.cons_append, lookupKV, Ne.symm h.1, ↓reduceIte]
    exact lookupKV_append_notin p xs h.2

theorem gsCompare_of_not_lt {a b : GoString} (hne : a ≠ b) (h : gsLt a b = false) :
    gsCompare a b = 1 := by
  have hr := gsCompare_range a b
  have h0 : gsCompare a b ≠ 0 := fun e => hne (gsCompare_eq_zero a b e)
  have h1 : gsCompare a b ≠ -1 := fun e => by rw [(gsLt_iff a b).2 e] at h; cases h
  omega

theorem gsLt_of_not_lt {a b : GoString} (hne : a ≠ b) (h : gsLt a b = false) : gsLt b a = true := by
  rw [gsLt_iff, gsCompare_swap, gsCompare_of_not_lt hne h]

/-- **`MapCompareUsing`'s step** on the key `k`, after the common prefix `p` of the two maps
`p ++ xs` and `p ++ ys`: the zip's next key is `k`. The comparison of the maps is decided as the
Go code decides it. -/
theorem mapCmp_step (p xs ys : List (GoString × UVal)) (k : GoString) (rest : List GoString)
    (hs1 : keysSorted (p ++ xs) = true) (hs2 : keysSorted (p ++ ys) = true)
    (hk : (zl xs ys).map (·.1) = k :: rest) :
    let c := listCmp (pairCmp UVal.compare) (p ++ xs) (p ++ ys)
    (xs = [] → c = -1) ∧
    (xs ≠ [] → ys = [] → c = 1) ∧
    (xs ≠ [] → ys ≠ [] → lookupKV k (p ++ xs) = none → c = 1) ∧
    (xs ≠ [] → ys ≠ [] → (lookupKV k (p ++ xs)).isSome → lookupKV k (p ++ ys) = none → c = -1) ∧
    (∀ a b, lookupKV k (p ++ xs) = some a → lookupKV k (p ++ ys) = some b →
      xs = (k, a) :: xs.tail ∧ ys = (k, b) :: ys.tail ∧
      c = if UVal.compare a b = 0 then listCmp (pairCmp UVal.compare) xs.tail ys.tail
          else UVal.compare a b) := by
  intro c
  have hc : c = listCmp (pairCmp UVal.compare) xs ys := listCmp_prefix _ pairCmp_self p xs ys
  have hsx := keysSorted_append_right p xs hs1
  have hsy := keysSorted_append_right p ys hs2
  -- `k` is not a key of `p`
  have hnd := zipKeys_nodup_law_holds (some (p ++ xs)) (some (p ++ ys))
    (fun _ h => by cases h; exact hs1) (fun _ h => by cases h; exact hs2)
  rw [zipKeys_zl] at hnd
  simp only [kvsOrEmpty, Option.getD_some, zl_prefix, List.map_append, List.map_map, hk] at hnd
  have hkp : k ∉ kvKeys p := by
    intro hm
    have := (List.nodup_append.1 hnd).2.2
    exact this k (by simpa [kvKeys, Function.comp_def] using hm) k (by simp) rfl
  rw [lookupKV_append_notin p xs hkp, lookupKV_append_notin p ys hkp, hc]
  clear hc c hnd hkp hs1 hs2
  match xs, ys, hsx, hsy, hk with
  | [], [], _, _, hk => simp [zl_nil_nil] at hk
  | [], (k', b) :: ys, _, _, hk => simp [listCmp, lookupKV]
  | (k', a) :: xs, [], _, _, hk => simp [listCmp, lookupKV]
  | (k1, a) :: xs, (k2, b) :: ys, hsx, hsy, hk =>
    unfold zl at hk
    simp only [List.length_cons] at hk
    rw [show xs.length + 1 + (ys.length + 1) + 1 = (xs.length + ys.length + 2) + 1 by omega] at hk
    simp only [zipLexical] at hk
    by_cases e : k1 = k2
    · subst e
      simp only [↓reduceIte, List.map_cons, List.cons.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      simp [lookupKV, listCmp, pairCmp, gsCompare_self]
    · by_cases hl : gsLt k1 k2 = true
      · simp only [e, hl, ↓reduceIte, List.map_cons, List.cons.injEq] at hk
        obtain ⟨rfl, -⟩ := hk
        have hn : lookupKV k1 ((k2, b) :: ys) = none := lookupKV_below hsy hl
        rw [hn]
        simp [lookupKV, listCmp, pairCmp, e, (gsLt_iff _ _).1 hl]
      · simp only [e, hl, ↓reduceIte, List.map_cons, List.cons.injEq, Bool.false_eq_true] at hk
        obtain ⟨rfl, -⟩ := hk
        have hl' := gsLt_of_not_lt e (by simpa using hl)
        have hn : lookupKV k2 ((k1, a) :: xs) = none := lookupKV_below hsx hl'
        rw [hn]
        simp [lookupKV, listCmp, pairCmp, e, gsCompare_of_not_lt e (by simpa using hl)]


/-! ## `UVal.mapLensOk` of sub-values -/

theorem mapLensOkL_mem {v : UVal} : ∀ {vs : List UVal}, v ∈ vs →
    UVal.mapLensOkL vs = true → UVal.mapLensOk v = true
  | [], h, _ => by simp at h
  | w :: vs, h, hok => by
    simp only [UVal.mapLensOkL, Bool.and_eq_true] at hok
    rcases List.mem_cons.1 h with rfl | h
    · exact hok.1
    · exact mapLensOkL_mem h hok.2

theorem mapLensOkM_mem {p : GoString × UVal} : ∀ {kvs : List (GoString × UVal)}, p ∈ kvs →
    UVal.mapLensOkM kvs = true → UVal.mapLensOk p.2 = true
  | [], h, _ => by simp at h
  | (k, w) :: kvs, h, hok => by
    simp only [UVal.mapLensOkM, Bool.and_eq_true] at hok
    rcases List.mem_cons.1 h with rfl | h
    · exact hok.1
    · exact mapLensOkM_mem h hok.2

theorem mapLensOk_map {kvs : List (GoString × UVal)} (h : UVal.mapLensOk (.map kvs) = true) :
    kvs.length ≤ 2 ^ 61 ∧ UVal.mapLensOkM kvs = true := by
  simpa [UVal.mapLensOk] using h

/-- `MapCompareUsing`'s callback step after the common prefix `p`: the zip's next key is `k`. -/
theorem mapCmp_next (ol or_ : Option (List (GoString × UVal))) (p xs ys : List (GoString × UVal))
    (k : GoString) (hL : kvsOrEmpty ol = p ++ xs) (hR : kvsOrEmpty or_ = p ++ ys)
    (hst : mapIterStep true (zipKeys ol or_) (p.map (·.1)) k) :
    ∃ rest, (zl xs ys).map (·.1) = k :: rest := by
  simp only [mapIterStep, ↓reduceIte] at hst
  rw [zipKeys_zl, hL, hR, zl_prefix, List.map_append, List.map_map] at hst
  have e : ((fun x : GoString × Option UVal × Option UVal => x.1) ∘
      fun e : GoString × UVal => (e.1, some e.2, some e.2)) = (·.1) := rfl
  rw [e, List.prefix_append_right_inj] at hst
  obtain ⟨t, ht⟩ := hst
  exact ⟨t, ht.symm⟩

/-- The zip ran to the end after the common prefix `p`: the two maps are equal. -/
theorem mapCmp_done (ol or_ : Option (List (GoString × UVal))) (p xs ys : List (GoString × UVal))
    (hL : kvsOrEmpty ol = p ++ xs) (hR : kvsOrEmpty or_ = p ++ ys)
    (hd : mapIterDone true (zipKeys ol or_) (p.map (·.1))) :
    kvsOrEmpty ol = kvsOrEmpty or_ := by
  simp only [mapIterDone, ↓reduceIte] at hd
  rw [zipKeys_zl, hL, hR, zl_prefix, List.map_append, List.map_map] at hd
  have e : ((fun x : GoString × Option UVal × Option UVal => x.1) ∘
      fun e : GoString × UVal => (e.1, some e.2, some e.2)) = (·.1) := rfl
  rw [e] at hd
  have h0 : (zl xs ys).map (·.1) = [] := by
    have := congrArg List.length hd; simp at this
    exact List.eq_nil_of_length_eq_zero (by simpa using this)
  obtain ⟨rfl, rfl⟩ := zl_ne_nil (List.map_eq_nil_iff.1 h0)
  rw [hL, hR]

/-- A small count as a Go `int`, compared to a length. -/
theorem W64_len_iff {n m : Nat} {v : w64} (hv : v.toInt = m) (hm : m ≤ 2 ^ 61) (hn : n ≤ m) :
    W64 n = v ↔ n = m := by
  constructor
  · intro h; subst h
    have : (W64 (n : Int)).toInt = n := by word
    omega
  · intro h; subst h; apply BitVec.eq_of_toInt_eq; rw [hv]; word

theorem W64_succ (n : Nat) (hn : n < 2 ^ 61) : W64 (n : Int) + W64 1 = W64 ((n + 1 : Nat) : Int) := by
  word

end ValueCmp

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

/-- A list view's `RangeUsing`, from the concrete specs of its two dynamic types. -/
theorem isListV_rangeDispatch
    (hR : value.listUnstructured.RangeUsing.spec (GF := GF))
    (hRP : value.listUnstructured.RangeUsing_ptr.spec (GF := GF))
    (l : value.List') (vs : List UVal) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV l vs ⊢
      ∃ i, ⌜l = .ok i⌝ ∗
        □ (∀ (a : value.Allocator), {{ isAlloc a }}
            (App (Val #(methods i.ty go!"RangeUsing" i.v)) (Val #a))
            {{ (r : value.ListRange), RET #r; isAlloc a ∗ ownRange r vs (-1) }}) := by
  iintro ⟨#Hpkg, #Hl⟩
  ihave %Hc := isListV_concrete_law_holds l vs $$ Hl
  rcases Hc with ⟨sl, rfl⟩ | ⟨p, rfl⟩
  · iexists _
    isplitr
    · ipureintro; rfl
    · imodintro
      iintro %a %Φ !> Ha HΦ
      iapply hR sl vs a $$ [Ha] [HΦ]
      · iframe; isplitr
        · iexact Hpkg
        · iexact Hl
      · iexact HΦ
  · iexists _
    isplitr
    · ipureintro; rfl
    · imodintro
      iintro %a %Φ !> Ha HΦ
      iapply hRP p vs a $$ [Ha] [HΦ]
      · iframe; isplitr
        · iexact Hpkg
        · iexact Hl
      · iexact HΦ

end lemmas

end smd
end EtcdGrove
end Perennial
