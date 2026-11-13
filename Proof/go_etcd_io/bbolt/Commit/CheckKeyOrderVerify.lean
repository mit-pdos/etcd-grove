/-
`compareKeys` and `verifyKeyOrder` of `tx_check.go` (U10h of `notes/bbolt-proof-plan.md`) on keys
of a reader's view: `verifyKeyOrder` sends nothing when the key is in order (at least the
previous key, above it when the index is not 0, below the bound).
-/
module

public import Proof.go_etcd_io.bbolt.Read.Src
public import Perennial.Spec.bytes.Compare
public import Proof.go_etcd_io.bbolt.Read.Open

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure

/-- The slice `s` is the bound `o`: `nil` for none, bytes of the view for a key. -/
def keyOpt (v : View) (s : GoSlice) : Option (List w8) → Prop
  | none => s = slice.nil
  | some k => inViewAt v s k

theorem inViewAt_ne_nil (v : View) (s : GoSlice) (k : List w8) (hb : 0 < v.base.addr)
    (h : inViewAt v s k) : s ≠ slice.nil := by
  intro e
  obtain ⟨⟨id, pg, off, -, -, -, hp⟩, -⟩ := h
  have : s.ptr = null := by rw [e]; rfl
  rw [this] at hp
  have h2 := congrArg Loc.addr hp
  simp [Loc.add, null] at h2
  omega

theorem compareResult_gt (a b : List w8) :
    sint.Z (bytes.compareResult a b) > sint.Z (W64 0) ↔ go.GoStringLt b a := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte]
    constructor
    · intro h'; exact absurd h' (by decide)
    · intro h'; exact absurd (go.goStringLt_trans h h') (go.goStringLt_irrefl _)
  · simp only [h, ↓reduceIte]
    by_cases he : a = b
    · subst he; simp only [↓reduceIte]
      constructor
      · intro h'; exact absurd h' (by decide)
      · intro h'; exact absurd h' (go.goStringLt_irrefl _)
    · simp only [he, ↓reduceIte]
      constructor
      · intro _
        refine Classical.byContradiction fun hn => he (go.goStringLt_eq_of_not_lt h hn)
      · intro _; decide

theorem compareResult_eq (a b : List w8) :
    bytes.compareResult a b = W64 0 ↔ a = b := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte]
    constructor
    · intro h'; exact absurd h' (by decide)
    · intro e; subst e; exact absurd h (go.goStringLt_irrefl _)
  · simp only [h, ↓reduceIte]
    by_cases he : a = b
    · simp [he]
    · simp only [he, ↓reduceIte, iff_false]; decide

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`compareKeys(left, right)`** is `bytes.Compare`. -/
abbrev compareKeys_ok.spec : Prop :=
  ∀ (sa sb : GoSlice) (da db : DFrac) (a b : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ sa ↦*{da} a ∗ sb ↦*{db} b }}
    (App (App (Val #(functions compareKeys [])) (Val #sa)) (Val #sb))
  {{ RET #(bytes.compareResult a b); sa ↦*{da} a ∗ sb ↦*{db} b }}

omit hos in
theorem compareKeys_ok.wp_proof (wp_C : bytes.Compare.spec (GF := GF) (hG := hG)) :
    compareKeys_ok.spec (GF := GF) (hG := hG) := by
  intro sa sb da db a b
  wp_start as ⟨Ha, Hb⟩
  wp_auto
  wp_apply wp_C $$ [Ha Hb] as ⟨Ha, Hb⟩
  · iframe
  iapply HΦ
  iframe

/-- **`verifyKeyOrder(pgId, pageType, index, key, previousKey, maxKeyOpen, ch, keyToString,
pagesStack)`** on keys of the view in order sends nothing: the key is not below the previous key
(`po`), above it if the index is not 0, and below the bound `mo`. -/
abbrev verifyKeyOrder_ok.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (pgId : w64)
    (pt : GoString) (index : w64) (key prev mx : GoSlice) (k : List w8)
    (po mo : Option (List w8)) (ch : Loc) (f : GoFunc) (stk : GoSlice),
  inViewAt v key k → keyOpt v prev po → keyOpt v mx mo →
  (index = W64 0 → keyGe po k) →
  (index ≠ W64 0 → 0 < sint.Z index ∧ ∃ p, po = some p ∧ go.GoStringLt p k) →
  keyLt k mo →
  {{ rdTxK (GF := GF) K tx src q T v }}
    (App (App (App (App (App (App (App (App (App (Val #(functions verifyKeyOrder []))
      (Val #pgId)) (Val #pt)) (Val #index)) (Val #key)) (Val #prev)) (Val #mx)) (Val #ch))
      (Val #f)) (Val #stk))
  {{ RET #(); rdTxK K tx src q T v }}

/-- Two slices of bytes of the view, read out of `rdTxK`, and back. -/
theorem rdTxK_view2_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (s1 s2 : GoSlice) (b1 b2 : List w8) (h1 : inViewAt v s1 b1) (h2 : inViewAt v s2 b2) :
    rdTxK (GF := GF) K tx src q T v ⊢
      ∃ d1 d2 : DFrac, s1 ↦*{d1} b1 ∗ s2 ↦*{d2} b2 ∗
        (s1 ↦*{d1} b1 -∗ s2 ↦*{d2} b2 -∗ rdTxK K tx src q T v) := by
  iintro Hk
  iapply rdTxK_src2_acc K tx src q T v s1 s2 Src.view Src.view b1 b2 (by intro e; cases e)
    (by intro e; cases e)
  iframe
  unfold srcOwn
  isplitr
  · ipureintro; exact h1
  · ipureintro; exact h2

set_option hygiene false in
/-- `verifyKeyOrder`'s bound check: the key is below `mo`. -/
local macro "vko_tail" : tactic => `(tactic| (
  cases mo with
  | none =>
    have hmn : mx = slice.nil := hmx
    subst hmn
    simp only [decide_true, Bool.not_true]
    wp_auto
    iapply HΦ; iframe
  | some h =>
    have hmn := inViewAt_ne_nil v mx h Hb hmx
    rw [decide_eq_false hmn]
    simp only [Bool.not_false]
    wp_auto
    icases rdTxK_view2_acc K tx src q T v key mx k h hkey hmx $$ Hk with ⟨%d1, %d2, H1, H2, Hback⟩
    wp_apply wp_ck key mx d1 d2 k h $$ [H1 H2] as ⟨H1, H2⟩
    · iframe
    ihave Hk := Hback $$ H1 H2
    rw [decide_eq_false (show ¬ sint.Z (bytes.compareResult k h) ≥ sint.Z (W64 0) by
      unfold bytes.compareResult; rw [ite_eq_left (hlt h rfl)]; decide)]
    wp_auto
    iapply HΦ; iframe))

theorem verifyKeyOrder_ok.wp_proof (wp_ck : compareKeys_ok.spec (GF := GF) (hG := hG)) :
    verifyKeyOrder_ok.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v pgId pt index key prev mx k po mo ch f stk hkey hprev hmx h0 hpos hlt
  wp_start as Hk
  ihave #Hpkg := rdTxK_pkgInit K tx src q T v $$ Hk
  ihave %Hb := rdTxK_base_pos K tx src q T v $$ Hk
  wp_auto
  by_cases hi0 : index = W64 0
  · rw [decide_eq_true hi0]
    wp_auto
    cases po with
    | none =>
      have : prev = slice.nil := hprev
      subst this
      simp only [decide_true, Bool.not_true]
      wp_auto
      rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z index by rw [hi0]; decide)]
      wp_auto
      vko_tail
    | some p =>
      have hpn := inViewAt_ne_nil v prev p Hb hprev
      rw [decide_eq_false hpn]
      simp only [Bool.not_false]
      wp_auto
      icases rdTxK_view2_acc K tx src q T v prev key p k hprev hkey $$ Hk
        with ⟨%d1, %d2, H1, H2, Hback⟩
      wp_apply wp_ck prev key d1 d2 p k $$ [H1 H2] as ⟨H1, H2⟩
      · iframe
      ihave Hk := Hback $$ H1 H2
      rw [decide_eq_false (show ¬ sint.Z (bytes.compareResult p k) > sint.Z (W64 0) by
        rw [compareResult_gt]; exact h0 hi0 p rfl)]
      wp_auto
      rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z index by rw [hi0]; decide)]
      wp_auto
      vko_tail
  · rw [decide_eq_false hi0]
    wp_auto
    obtain ⟨hip, p, rfl, hpk⟩ := hpos hi0
    rw [decide_eq_true (show sint.Z (W64 0) < sint.Z index from hip)]
    wp_auto
    icases rdTxK_view2_acc K tx src q T v prev key p k hprev hkey $$ Hk
      with ⟨%d1, %d2, H1, H2, Hback⟩
    wp_apply wp_ck prev key d1 d2 p k $$ [H1 H2] as ⟨H1, H2⟩
    · iframe
    ihave Hk := Hback $$ H1 H2
    have hcr : bytes.compareResult p k = W64 (-1) := by
      unfold bytes.compareResult; rw [ite_eq_left hpk]
    rw [hcr]
    wp_auto
    vko_tail

end spec

end bbolt
end EtcdGrove
end Perennial
