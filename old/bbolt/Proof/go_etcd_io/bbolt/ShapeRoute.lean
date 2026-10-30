/-
A cursor's descent by a key (`WriteTxShape.lean`'s `routes`, `kroute`): the index a branch's
search picks (`searchNode`, `searchPage`) is the entry `routes` names.

`sort.Search`'s spec (Perennial's `sort.wp_Search`) does not say that the predicate was called
at the index it returns, which `searchNode`/`searchPage` need: their `exact` flag is set by the
predicate when a key equals the searched one, and the index steps back unless it is set. So
`wp_Search_last` restates `sort.Search` with an invariant `J` indexed by the last index at which
the predicate returned true (`n` before any): the result is that index.
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxShape
public import Proof.go_etcd_io.bbolt.KeyOrder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

/-! ### `sort.Search`, with the last index the predicate held at -/

section sortlast
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [sort_sem : sort.Assumptions]

/-- The predicate code implements `f` on `[0, n)`, with an invariant `J o` indexed by the last
index `o` at which it returned true: a call at `i` returning true moves it to `i`. -/
def predImplementsJ (f_code : GoFunc) (f : Int → Bool) (n : Int) (J : Int → IProp GF) :
    IProp GF :=
  iprop(∀ (i : w64) (o : Int),
    {{ J o ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < n⌝ }}
      (App (Val #f_code) (Val #i))
    {{ (r : Bool), RET #r; ∃ o', J o' ∗
        ⌜r = f (sint.Z i) ∧ (f (sint.Z i) = true → o' = sint.Z i) ∧
          (f (sint.Z i) = false → o' = o)⌝ }})

instance predImplementsJ_persistent (f_code : GoFunc) (f : Int → Bool) (n : Int)
    (J : Int → IProp GF) : Persistent (predImplementsJ f_code f n J) := by
  unfold predImplementsJ; infer_instance

set_option maxRecDepth 20000 in
/-- `sort.wp_Search`, with the invariant at the index it returns. -/
theorem wp_Search_last (n : w64) (f_code : GoFunc) (f : Int → Bool) (J : Int → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        ⌜0 ≤ sint.Z n⌝ ∗
        predImplementsJ f_code f (sint.Z n) J ∗
        J (sint.Z n) ∗
        ⌜sort.IsMonoPred f (sint.Z n)⌝ }}
      (App (App (Val (@! sort.Search)) (Val #n)) (Val #f_code))
    {{ (i : w64), RET #i;
        J (sint.Z i) ∗
        ⌜0 ≤ sint.Z i⌝ ∗
        ⌜sint.Z i < sint.Z n → f (sint.Z i) = true⌝ ∗
        ⌜(∀ i, 0 ≤ i ∧ i < sint.Z n → f i = false) → sint.Z i = sint.Z n⌝ ∗
        ⌜∀ k, 0 ≤ k ∧ k < sint.Z i → f k = false⌝ }} := by
  wp_start as ⟨%Hpos, #Hf, I, %Hvalid⟩
  wp_auto
  have Hvalid := sort.isValidPred_adapted f (sint.Z n) Hpos Hvalid
  obtain ⟨Hmono, Hneg, Hn⟩ := Hvalid
  unfold predImplementsJ
  ihave HI : (∃ (i j : w64),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "I" ∷ J (sint.Z j) ∗
      "%Hbounds" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z n⌝ ∗
      "%Hi_prop" ∷ ⌜sort.adaptPred f (sint.Z n) (sint.Z i - 1) = false⌝ ∗
      "%Hj_prop" ∷ ⌜sort.adaptPred f (sint.Z n) (sint.Z j) = true⌝ : IProp GF) $$ [i j I]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, Hn⟩
    rw [show sint.Z (W64 0) - 1 = -1 by word, Hneg]
  wp_for HI
  wp_if_destruct
  · have Hj : sint.Z i ≤ sint.Z ((i + j) >>> W64 1) ∧ sint.Z ((i + j) >>> W64 1) < sint.Z j := by
      rw [sort.shiftr_1_eq_div]; word'
    wp_apply Hf $$ %((i + j) >>> W64 1) %(sint.Z j) [I] with %r ⟨%o', I, %Hf_res⟩
    · iframe I; ipureintro; omega
    obtain ⟨Hf_result, Ho1, Ho2⟩ := Hf_res
    generalize (i + j) >>> W64 1 = h at Hj Hf_result Ho1 Ho2 ⊢
    have Had : sort.adaptPred f (sint.Z n) (sint.Z h) = f (sint.Z h) :=
      sort.adaptPred_bounded _ _ _ (by omega)
    cases r
    · simp only [Bool.not_false]
      have Ho : o' = sint.Z j := Ho2 Hf_result.symm
      subst Ho
      wp_auto
      wp_for_post
      iframe
      iexists (h + W64 1), j
      iframe
      ipureintro
      refine ⟨by word, ?_, Hj_prop⟩
      have : sint.Z (h + W64 1) - 1 = sint.Z h := by word
      rw [this, Had, ← Hf_result]
    · simp only [Bool.not_true]
      have Ho : o' = sint.Z h := Ho1 Hf_result.symm
      subst Ho
      wp_auto
      wp_for_post
      iframe
      iexists i, h
      iframe
      ipureintro
      exact ⟨by word, Hi_prop, by rw [Had, ← Hf_result]⟩
  · have Hij : sint.Z i = sint.Z j := by omega
    rw [← Hij]
    iapply HΦ
    iframe I
    ipureintro
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro Hilt
      rw [← Hij, sort.adaptPred_bounded _ _ _ (by omega)] at Hj_prop
      exact Hj_prop
    · intro Hno_true
      by_cases hlt : sint.Z i < sint.Z n
      · rw [← Hij, sort.adaptPred_bounded _ _ _ (by omega)] at Hj_prop
        have := Hno_true (sint.Z i) (by omega)
        simp_all
      · omega
    · intro k Hk
      by_cases hk : k = sint.Z i - 1
      · subst hk; rwa [sort.adaptPred_bounded _ _ _ (by omega)] at Hi_prop
      · cases hfk : f k
        · rfl
        · have := Hmono k (sint.Z i - 1) (by omega)
            (by rw [sort.adaptPred_bounded _ _ _ (by omega)]; exact hfk)
          simp_all

end sortlast

/-! ### The index a branch's search picks -/

section route
variable [ext : FfiSyntax]

theorem goStringLt_irrefl_r : ∀ (a : List w8), ¬ go.GoStringLt a a
  | [], h => by cases h
  | x :: xs, h => by
    cases h with
    | cons h' => exact goStringLt_irrefl_r xs h'
    | rel h' => exact Int.lt_irrefl _ h'

theorem goStringLt_trichot_r : ∀ (a b : List w8), go.GoStringLt a b ∨ a = b ∨ go.GoStringLt b a
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl List.Lex.nil
  | _ :: _, [] => Or.inr (Or.inr List.Lex.nil)
  | x :: xs, y :: ys => by
    rcases Int.lt_trichotomy (uint.Z x) (uint.Z y) with h | h | h
    · exact Or.inl (List.Lex.rel h)
    · have hxy : x = y := by
        have := congrArg Int.toNat h
        apply BitVec.eq_of_toNat_eq; simpa [uint.Z] using this
      subst hxy
      rcases goStringLt_trichot_r xs ys with h' | h' | h'
      · exact Or.inl (List.Lex.cons h')
      · exact Or.inr (Or.inl (by rw [h']))
      · exact Or.inr (Or.inr (List.Lex.cons h'))
    · exact Or.inr (Or.inr (List.Lex.rel h))

theorem goStringLt_asymm_b {a b : List w8} (h : go.GoStringLt a b) : ¬ go.GoStringLt b a :=
  fun h' => goStringLt_irrefl_r a (goStringLt_trans h h')

/-- `idx` is where `kb` goes among the keys `L`: every key before it is below `kb`, the one at
it (if any) is not (`sort.Search`'s result, over keys that increase). -/
def keysIdx (L : List (List w8)) (kb : List w8) (idx : Nat) : Prop :=
  idx ≤ L.length ∧ (∀ (k : Nat) a, k < idx → L[k]? = some a → go.GoStringLt a kb) ∧
  (∀ a, L[idx]? = some a → ¬ go.GoStringLt a kb)

/-- The keys `L` increase. -/
def keysSorted (L : List (List w8)) : Prop :=
  ∀ (i j : Nat) a b, i < j → L[i]? = some a → L[j]? = some b → go.GoStringLt a b

/-- What `searchNode`/`searchPage` pick, over the branch's keys `L` (increasing, at least one):
`idx` is `sort.Search`'s result (`keysIdx`), `e` the `exact` flag (set only for a key equal to
`kb`, and set if the key at `idx` is). The index `idx` if `exact`, else the one before (unless
`idx = 0`), is the entry `routes` names. -/
theorem routes_search (L : List (List w8)) (kb : List w8) (idx : Nat) (e : Bool)
    (hs : keysSorted L) (hn : 0 < L.length) (hk : keysIdx L kb idx)
    (hT : e = true → ∃ h : Nat, L[h]? = some kb)
    (hF : L[idx]? = some kb → e = true) :
    (e = true → routes L idx kb) ∧ (e = false → 0 < idx → routes L (idx - 1) kb) ∧
    (e = false → idx = 0 → routes L 0 kb) := by
  obtain ⟨hidx, hbelow, hat⟩ := hk
  refine ⟨fun he => ?_, fun he hpos => ?_, fun he h0 => ?_⟩
  · obtain ⟨h, hh⟩ := hT he
    have hhl : h < L.length := (List.getElem?_eq_some_iff.1 hh).1
    have hhi : h = idx := by
      rcases Nat.lt_trichotomy h idx with hlt | heq | hgt
      · exact absurd (hbelow h kb hlt hh) (goStringLt_irrefl_r kb)
      · exact heq
      · have hil : idx < L.length := by omega
        have := hs idx h _ kb hgt (List.getElem?_eq_getElem hil) hh
        exact absurd this (hat _ (List.getElem?_eq_getElem hil))
    subst hhi
    refine ⟨hhl, Or.inr ⟨kb, hh, goStringLt_irrefl_r kb⟩, fun kn hkn => hs h (h + 1) kb kn
      (by omega) hh hkn⟩
  · refine ⟨by omega, Or.inr ⟨_, List.getElem?_eq_getElem (by omega),
      goStringLt_asymm_b (hbelow _ _ (by omega) (List.getElem?_eq_getElem (by omega)))⟩, ?_⟩
    intro kn hkn
    rw [show idx - 1 + 1 = idx by omega] at hkn
    rcases goStringLt_trichot_r kn kb with h | h | h
    · exact absurd h (hat kn hkn)
    · subst h; rw [hF hkn] at he; cases he
    · exact h
  · subst h0
    refine ⟨hn, Or.inl rfl, fun kn hkn => ?_⟩
    have h1 : 1 < L.length := (List.getElem?_eq_some_iff.1 hkn).1
    have hk0 := hat _ (List.getElem?_eq_getElem hn)
    have hlt := hs 0 1 _ kn (by omega) (List.getElem?_eq_getElem hn) hkn
    rcases goStringLt_trichot_r (L[0]'hn) kb with h | h | h
    · exact absurd h hk0
    · rw [← h]; exact hlt
    · exact goStringLt_trans h hlt

/-- The `sort.Search` predicate "key not below `kb`" (`entryGE`, `branchGE`, `leafGE`). -/
theorem geTrue_iff (a kb : List w8) :
    decide (bytes.compareResult a kb ≠ W64 (-1)) = true ↔ ¬ go.GoStringLt a kb := by
  simp only [decide_eq_true_eq, ne_eq, compareResult_eq_neg1]

theorem geFalse_iff (a kb : List w8) :
    decide (bytes.compareResult a kb ≠ W64 (-1)) = false ↔ go.GoStringLt a kb := by
  simp only [decide_eq_false_iff_not, ne_eq, Classical.not_not, compareResult_eq_neg1]

/-- Keys given by a function `g` on `[0, n)`. -/
def keysFn (L : List (List w8)) (n : Nat) (g : Nat → List w8) : Prop :=
  L.length = n ∧ ∀ k, k < n → L[k]? = some (g k)

theorem keysFn_get {L : List (List w8)} {n : Nat} {g : Nat → List w8} (h : keysFn L n g) {k : Nat}
    {a : List w8} (hk : L[k]? = some a) : k < n ∧ a = g k := by
  have hl : k < L.length := (List.getElem?_eq_some_iff.1 hk).1
  have := h.2 k (by rw [← h.1]; exact hl)
  rw [hk] at this
  exact ⟨by rw [← h.1]; exact hl, Option.some.inj this⟩

theorem keysFn_range (n : Nat) (g : Nat → List w8) : keysFn ((List.range n).map g) n g :=
  ⟨by simp, fun k hk => by simp [List.getElem?_map, List.getElem?_range hk]⟩

theorem keysFn_ws (ws : List WEntry) : keysFn (ws.map WEntry.key) ws.length (wKey ws) :=
  ⟨by simp, fun k hk => by simp [List.getElem?_map, wKey, List.getElem?_eq_getElem hk]⟩

theorem keysSorted_fn {L : List (List w8)} {n : Nat} {g : Nat → List w8} (h : keysFn L n g)
    (hs : ∀ i j, i < j → j < n → go.GoStringLt (g i) (g j)) : keysSorted L := by
  intro i j a b hij ha hb
  obtain ⟨-, rfl⟩ := keysFn_get h ha
  obtain ⟨hj, rfl⟩ := keysFn_get h hb
  exact hs i j hij hj

/-- `sort.Search`'s result over keys `g` on `[0, n)` (the predicate "not below `kb`"). -/
theorem keysIdx_search {L : List (List w8)} {n : Nat} {g : Nat → List w8} (h : keysFn L n g)
    (kb : List w8) (idx : w64) (H0 : 0 ≤ sint.Z idx) (Hle : sint.Z idx ≤ (n : Int))
    (Hfound : sint.Z idx < (n : Int) → ¬ go.GoStringLt (g (sint.Z idx).toNat) kb)
    (Hgt : ∀ k : Int, 0 ≤ k ∧ k < sint.Z idx → go.GoStringLt (g k.toNat) kb) :
    keysIdx L kb (sint.Z idx).toNat := by
  refine ⟨by rw [h.1]; omega, fun k a hk ha => ?_, fun a ha => ?_⟩
  · obtain ⟨-, rfl⟩ := keysFn_get h ha
    have := Hgt (k : Int) ⟨by omega, by omega⟩
    simpa using this
  · obtain ⟨hl, rfl⟩ := keysFn_get h ha
    exact Hfound (by omega)

/-! ### The descent's leaf index -/

/-- The stack elements `es`, from position `pid` down, end at a leaf whose index is where `k`
goes among its keys (`Cursor.search`'s `nsearch`). -/
def kseek (W : WView) (B : BRec) (k : List w8) : w64 → List elemRef → Prop
  | _, [] => False
  | pid, [r] => ∃ ks, keysAt W B pid = some ks ∧ keysIdx ks k (sint.Z r.index').toNat
  | pid, r :: r2 :: rs => ∃ cs c, kidsAt W B pid = some (false, cs) ∧
      cs[(sint.Z r.index').toNat]? = some c ∧ kseek W B k c (r2 :: rs)

end route

end bbolt
end EtcdGrove
end Perennial
