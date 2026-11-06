/-
Lean-first (no Rocq counterpart).

# linkvtxn: the total order on the model's values (`cmpInt` ... `cmpStore`)

`examples/etcd/txnlin/linkvtxn.go` keeps a model state sorted by `cmpConfig`, a total order on
configurations built field by field from `cmpInt` (signed) and `cmpStr` (Go's `<` on strings).
Here are their pure forms, as `Ordering`s (`ordW` the `int` a Go function returns for one): `cmpZ`,
`cmpW`, `cmpS`, and, from Lean core's `compareLex` (one field, then the next) and
`List.compareLex`, `cmpTOpO`, `cmpCmpO`, `cmpInO`, `cmpVRO`, `cmpEntO`, `cmpStO`; each is a
`Std.TransCmp` and a `Std.LawfulEqCmp` (`.eq` exactly on equal values), which is what a binary
search over a list sorted by it needs (`addConfig.lean`). `GCfg`'s order, `cmpCfgO`, is in
`Steps.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.ModelLemmas
public import Perennial.Golang.Theory.String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin
open Std

/-! ## The generic pieces -/

/-- The `int` a Go comparison returns for an `Ordering`: -1, 0 or 1. -/
def ordW : Ordering → w64
  | .lt => W64 (-1)
  | .eq => W64 0
  | .gt => W64 1

theorem ordW_eq_zero (o : Ordering) : ordW o = W64 0 ↔ o = .eq := by
  cases o <;> simp [ordW] <;> decide

theorem ordW_neg (o : Ordering) : sint.Z (ordW o) < 0 ↔ o = .lt := by
  cases o <;> simp [ordW] <;> decide

/-- A Go comparison's `if c != 0 { return c }`: returned. -/
theorem then_of_ne {o : Ordering} (p : Ordering) (h : ¬ ordW o = W64 0) : o.then p = o := by
  cases o <;> simp_all [ordW, Ordering.then]

/-- A Go comparison's `if c != 0 { return c }`: not returned. -/
theorem then_of_eq {o : Ordering} (p : Ordering) (h : ordW o = W64 0) : o.then p = p := by
  rw [(ordW_eq_zero o).1 h]; rfl

/-- The comparison of `f a` and `f b` by `cmp`. -/
def cmpOn {α β : Type} (f : α → β) (cmp : β → β → Ordering) (a b : α) : Ordering := cmp (f a) (f b)

instance {α β : Type} {f : α → β} {cmp : β → β → Ordering} [OrientedCmp cmp] :
    OrientedCmp (cmpOn f cmp) where
  eq_swap := OrientedCmp.eq_swap (cmp := cmp)

instance {α β : Type} {f : α → β} {cmp : β → β → Ordering} [TransCmp cmp] :
    TransCmp (cmpOn f cmp) where
  isLE_trans := TransCmp.isLE_trans (cmp := cmp)

theorem cmpOn_eq {α β : Type} {f : α → β} {cmp : β → β → Ordering} [LawfulEqCmp cmp] {a b : α}
    (h : cmpOn f cmp a b = .eq) : f a = f b := LawfulEqCmp.eq_of_compare (cmp := cmp) h

/-- Integers' order. -/
def cmpZ (a b : Int) : Ordering := if a < b then .lt else if b < a then .gt else .eq

instance : TransCmp cmpZ where
  eq_swap {a b} := by
    unfold cmpZ
    rcases Int.lt_trichotomy a b with h | rfl | h
    · simp [h, Int.lt_asymm h]
    · simp
    · simp [h, Int.lt_asymm h]
  isLE_trans {a b c} h1 h2 := by
    have key : ∀ x y : Int, (cmpZ x y).isLE ↔ x ≤ y := by
      intro x y; unfold cmpZ; split <;> (try split) <;> simp <;> omega
    rw [key] at *; omega

instance : LawfulEqCmp cmpZ where
  compare_self {a} := by simp [cmpZ]
  eq_of_compare {a b} h := by
    unfold cmpZ at h
    by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp_all <;> omega

/-- `cmpInt`'s order: signed. -/
def cmpW (a b : w64) : Ordering := cmpZ (sint.Z a) (sint.Z b)

instance : TransCmp cmpW := inferInstanceAs (TransCmp (cmpOn (fun w : w64 => sint.Z w) cmpZ))

instance : LawfulEqCmp cmpW where
  compare_self {a} := ReflCmp.compare_self (cmp := cmpZ)
  eq_of_compare {a b} h := by
    have := LawfulEqCmp.eq_of_compare (cmp := cmpZ) h
    word

/-- `cmpStr`'s order: Go's `<` on strings. -/
def cmpS (a b : GoString) : Ordering :=
  if go.GoStringLt a b then .lt else if go.GoStringLt b a then .gt else .eq

instance : TransCmp cmpS where
  eq_swap {a b} := by
    unfold cmpS
    by_cases h1 : go.GoStringLt a b
    · simp [h1, go.goStringLt_asymm h1]
    · by_cases h2 : go.GoStringLt b a <;> simp [h1, h2]
  isLE_trans {a b c} h1 h2 := by
    unfold cmpS at *
    by_cases e1 : go.GoStringLt a b
    · by_cases e3 : go.GoStringLt b c
      · simp [go.goStringLt_trans e1 e3]
      · by_cases e4 : go.GoStringLt c b
        · simp [e3, e4] at h2
        · have := go.goStringLt_eq_of_not_lt e3 e4; subst this; simp [e1]
    · by_cases e2 : go.GoStringLt b a
      · simp [e1, e2] at h1
      · have := go.goStringLt_eq_of_not_lt e1 e2; subst this; exact h2

instance : LawfulEqCmp cmpS where
  compare_self {a} := by simp [cmpS, go.goStringLt_irrefl]
  eq_of_compare {a b} h := by
    unfold cmpS at h
    by_cases h1 : go.GoStringLt a b <;> by_cases h2 : go.GoStringLt b a <;> simp_all
    exact go.goStringLt_eq_of_not_lt h1 h2

/-! ## The records' orders (field by field, as the Go functions) -/

section go
variable [GooseExts]

/-- `cmpTOp`'s order. -/
def cmpTOpO : TOp → TOp → Ordering :=
  compareLex (cmpOn TOp.Kind' cmpW) (compareLex (cmpOn TOp.Key' cmpS) (cmpOn TOp.Val' cmpS))

instance : TransCmp cmpTOpO := by unfold cmpTOpO; infer_instance

instance : LawfulEqCmp cmpTOpO where
  compare_self {a} := ReflCmp.compare_self (cmp := cmpTOpO)
  eq_of_compare {a b} h := by
    simp only [cmpTOpO, compareLex_eq_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    cases a; cases b
    simp only [TOp.mk.injEq]
    exact ⟨cmpOn_eq h1, cmpOn_eq h2, cmpOn_eq h3⟩

/-- `cmpCmp`'s order. -/
def cmpCmpO : Cmp → Cmp → Ordering :=
  compareLex (cmpOn Cmp.Kind' cmpW) (compareLex (cmpOn Cmp.Key' cmpS)
    (compareLex (cmpOn Cmp.Val' cmpS) (cmpOn Cmp.Num' cmpW)))

instance : TransCmp cmpCmpO := by unfold cmpCmpO; infer_instance

instance : LawfulEqCmp cmpCmpO where
  compare_self {a} := ReflCmp.compare_self (cmp := cmpCmpO)
  eq_of_compare {a b} h := by
    simp only [cmpCmpO, compareLex_eq_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    cases a; cases b
    simp only [Cmp.mk.injEq]
    exact ⟨cmpOn_eq h1, cmpOn_eq h2, cmpOn_eq h3, cmpOn_eq h4⟩

/-- `cmpInput`'s order. -/
def cmpInO : Input → Input → Ordering :=
  compareLex (cmpOn Input.Kind' cmpW) (compareLex (cmpOn Input.Key' cmpS)
    (compareLex (cmpOn Input.Val' cmpS) (compareLex (cmpOn Input.NCmps' cmpW)
    (compareLex (cmpOn Input.Cmp0' cmpCmpO) (compareLex (cmpOn Input.NThen' cmpW)
    (compareLex (cmpOn Input.Then0' cmpTOpO) (compareLex (cmpOn Input.Then1' cmpTOpO)
    (compareLex (cmpOn Input.Then2' cmpTOpO) (compareLex (cmpOn Input.NElse' cmpW)
    (cmpOn Input.Else0' cmpTOpO))))))))))

instance : TransCmp cmpInO := by unfold cmpInO; infer_instance

instance : LawfulEqCmp cmpInO where
  compare_self {a} := ReflCmp.compare_self (cmp := cmpInO)
  eq_of_compare {a b} h := by
    simp only [cmpInO, compareLex_eq_eq] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    cases a; cases b
    simp only [Input.mk.injEq]
    exact ⟨cmpOn_eq h1, cmpOn_eq h2, cmpOn_eq h3, cmpOn_eq h4, cmpOn_eq h5, cmpOn_eq h6,
      cmpOn_eq h7, cmpOn_eq h8, cmpOn_eq h9, cmpOn_eq h10, cmpOn_eq h11⟩

/-- `cmpVR`'s order. -/
def cmpVRO : VR → VR → Ordering :=
  compareLex (cmpOn VR.Val' cmpS) (compareLex (cmpOn VR.Mod' cmpW) (cmpOn VR.Ver' cmpW))

instance : TransCmp cmpVRO := by unfold cmpVRO; infer_instance

instance : LawfulEqCmp cmpVRO where
  compare_self {a} := ReflCmp.compare_self (cmp := cmpVRO)
  eq_of_compare {a b} h := by
    simp only [cmpVRO, compareLex_eq_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    cases a; cases b
    simp only [VR.mk.injEq]
    exact ⟨cmpOn_eq h1, cmpOn_eq h2, cmpOn_eq h3⟩

/-- A store entry's order (`cmpStore`'s loop body: the key, then the value). -/
def cmpEntO : entry → entry → Ordering :=
  compareLex (cmpOn entry.key' cmpS) (cmpOn entry.r' cmpVRO)

instance : TransCmp cmpEntO := by unfold cmpEntO; infer_instance

instance : LawfulEqCmp cmpEntO where
  compare_self {a} := ReflCmp.compare_self (cmp := cmpEntO)
  eq_of_compare {a b} h := by
    simp only [cmpEntO, compareLex_eq_eq] at h
    obtain ⟨h1, h2⟩ := h
    cases a; cases b
    simp only [entry.mk.injEq]
    exact ⟨cmpOn_eq h1, cmpOn_eq h2⟩

/-- Lists compared by length, then element by element (`cmpStore`'s and `cmpConfig`'s). -/
def cmpLenLex {α : Type} (cmp : α → α → Ordering) : List α → List α → Ordering :=
  compareLex (cmpOn (fun l : List α => (l.length : Int)) cmpZ) (List.compareLex cmp)

instance {α : Type} {cmp : α → α → Ordering} [TransCmp cmp] : TransCmp (cmpLenLex cmp) := by
  unfold cmpLenLex; infer_instance

instance {α : Type} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp] :
    LawfulEqCmp (cmpLenLex cmp) where
  compare_self {a} := ReflCmp.compare_self (cmp := cmpLenLex cmp)
  eq_of_compare {a b} h := by
    simp only [cmpLenLex, compareLex_eq_eq] at h
    exact LawfulEqCmp.eq_of_compare (cmp := List.compareLex cmp) h.2

/-- `List.compareLex` of two lists with a common prefix. -/
theorem compareLex_append_left {α : Type} {cmp : α → α → Ordering} [ReflCmp cmp]
    (p a b : List α) : List.compareLex cmp (p ++ a) (p ++ b) = List.compareLex cmp a b := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [List.cons_append, List.compareLex_cons_cons, ReflCmp.compare_self, ih,
      Ordering.eq_then]

/-- `List.compareLex` of two lists equal before index `i`: from their elements at `i` on. -/
theorem compareLex_at {α : Type} {cmp : α → α → Ordering} [ReflCmp cmp] (a b : List α) (i : Nat)
    (x y : α) (h : a.take i = b.take i) (hx : a[i]? = some x) (hy : b[i]? = some y) :
    List.compareLex cmp a b = (cmp x y).then (List.compareLex cmp (a.drop (i + 1)) (b.drop (i + 1))) := by
  have ha : a = a.take i ++ x :: a.drop (i + 1) := by
    have hi : i < a.length := (List.getElem?_eq_some_iff.1 hx).1
    rw [List.getElem?_eq_getElem hi] at hx; cases hx
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hb : b = b.take i ++ y :: b.drop (i + 1) := by
    have hi : i < b.length := (List.getElem?_eq_some_iff.1 hy).1
    rw [List.getElem?_eq_getElem hi] at hy; cases hy
    rw [List.getElem_cons_drop, List.take_append_drop]
  conv => lhs; rw [ha, hb, h]
  rw [compareLex_append_left, List.compareLex_cons_cons]

/-- `cmpStore`'s order: the revision, then the entries. -/
def cmpStO : GSt → GSt → Ordering :=
  compareLex (cmpOn GSt.rev cmpW) (cmpOn GSt.kvs (cmpLenLex cmpEntO))

instance : TransCmp cmpStO := by unfold cmpStO; infer_instance

instance : LawfulEqCmp cmpStO where
  compare_self {a} := ReflCmp.compare_self (cmp := cmpStO)
  eq_of_compare {a b} h := by
    simp only [cmpStO, compareLex_eq_eq] at h
    obtain ⟨h1, h2⟩ := h
    cases a; cases b
    simp only [GSt.mk.injEq]
    exact ⟨cmpOn_eq h2, cmpOn_eq h1⟩

end go

end etcd_txnlin
end EtcdGrove
end Perennial
