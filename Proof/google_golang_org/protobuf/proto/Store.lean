/-
**The generic loop-free store** (per-type message models, stage A prototype, `[v5]`/`[v5a]` V of
the Scope): a receive model's satisfiability (`PbType.Sat`, `ProtoMsg.ReqSat`/`RepSat`,
`StreamMsg.Sat`) is a WP of `storeInto ty l (T.tree m)`, a GooseLang expression this file defines
once, by structural recursion on a tree of values (`VTree`): typed allocations (`ptr`), slice and
struct literals, and `let`s binding their elements; no `rec`, no `for`, no call of any Go function.
An instance gives only the pure function `T.tree : M → VTree` (its normalization: empty bytes as
`nil`, a proto3 zero unset), so the store's termination never depends on an instance, and an
instance cannot prove its `Sat` with a diverging copy.

- `storeTree t`: the expression that builds `t`'s value (its pointers allocated);
- `storeInto ty l t`: the typed store of that value at `l`;
- `treeWp t Φ`: what `storeTree t` needs, node by node (the obligations of its allocations and
  literals), and `storeTree_wp : treeWp t Φ ⊢ WP storeTree t {{ Φ }}`, proved once;
- the typed forms: `treeWp_ptr` (a pointer node over a typed points-to, `IntoValTyped`),
  `treeWp_bytes` (a slice node of values, `ownSlice`), `storeInto_wp` (the typed store).

A struct literal's step is the struct type's (its `TypeAssumptions`): an instance discharges its
`strct` nodes' obligations with `wp_auto`, at the struct's own type.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-! ## The tree and its store -/

section syntax_
variable [GooseExts]

/-- **A tree of values to store**: a value (`leaf`), a fresh pointer to a tree's value, typed
(`ptr ty t`: `GoAlloc ty`), a slice literal of element type `ty` (`slice`), or a struct literal of
type `ty` with the fields `fs` (name and type) set to the trees `ts` (`strct`; the fields past
`ts`'s length are left out). -/
inductive VTree where
  | leaf (v : val)
  | ptr (ty : go.GoType) (t : VTree)
  | slice (ty : go.GoType) (ts : List VTree)
  | strct (ty : go.GoType) (fs : List (GoString × go.GoType)) (ts : List VTree)

instance : Inhabited VTree := ⟨.leaf (.LitV .LitUnit)⟩

/-- The name the store binds its `i`th element to. -/
def vname (i : Nat) : String := String.ofList ('$' :: 't' :: List.replicate i 'v')

theorem vname_inj {i j : Nat} (h : vname i = vname j) : i = j := by
  have := congrArg String.length h
  simpa [vname] using this

/-- A literal's elements: the `i`th of `kes` (its key, a field name or none, and its type) holding
the expression `σ i`. -/
def kesσ : List (Option GoString × go.GoType) → Nat → (Nat → Expr) → List keyed_element
  | [], _, _ => []
  | (k, t) :: r, i, σ => KeyedElement (k.map KeyField) (ElementExpression t (σ i)) :: kesσ r (i + 1) σ

/-- The composite literal of type `lty` with the elements `kes` holding `σ`. -/
def litBody (lty : go.GoType) (kes : List (Option GoString × go.GoType)) (σ : Nat → Expr) : Expr :=
  App (Val (GoInstruction (CompositeLiteral lty))) (LiteralValue (kesσ kes 0 σ))

/-- A slice literal's keys: none, `n` times, of type `ty`. -/
def sliceKes (ty : go.GoType) (n : Nat) : List (Option GoString × go.GoType) :=
  List.replicate n (none, ty)

/-- A struct literal's keys: its fields, as many as its trees. -/
def strctKes (fs : List (GoString × go.GoType)) (n : Nat) : List (Option GoString × go.GoType) :=
  (fs.take n).map fun p => (some p.1, p.2)

/-- The elements bound to their names. -/
def varσ : Nat → Expr := fun j => Var (vname j)

mutual
/-- **The expression that builds a tree's value** (structural recursion; loop-free). -/
def storeTree : VTree → Expr
  | .leaf v => Val v
  | .ptr ty t => App (Val (GoInstruction (GoAlloc ty))) (storeTree t)
  | .slice ty ts => storeTrees ts 0 (litBody (go.SliceType ty) (sliceKes ty ts.length) varσ)
  | .strct ty fs ts => storeTrees ts 0 (litBody ty (strctKes fs ts.length) varσ)

/-- The trees `ts` evaluated in order, the `j`th bound to `vname (i + j)`, then `e`. -/
def storeTrees : List VTree → Nat → Expr → Expr
  | [], _, e => e
  | t :: ts, i, e => Let (BNamed (vname i)) (storeTree t) (storeTrees ts (i + 1) e)
end

/-- **The typed store of a tree's value at `l`.** -/
def storeInto (ty : go.GoType) (l : Loc) (t : VTree) [GoGlobalContext] : Expr :=
  App (Val (GoInstruction (GoStore ty))) (Pair (Val #l) (storeTree t))

/-! ### Substitution: the store is closed -/

theorem substKeyedElements_kesσ (x : String) (v : val) :
    ∀ (kes : List (Option GoString × go.GoType)) (i : Nat) (σ : Nat → Expr),
      substKeyedElements x v (kesσ kes i σ) = kesσ kes i (fun j => subst x v (σ j))
  | [], _, _ => by simp [kesσ, substKeyedElements]
  | (k, t) :: r, i, σ => by
    cases k <;>
      simp [kesσ, substKeyedElements, substKeyedElement, substOptKey, substElement,
        substKeyedElements_kesσ x v r (i + 1) σ]

theorem subst_litBody (x : String) (v : val) (lty : go.GoType)
    (kes : List (Option GoString × go.GoType)) (σ : Nat → Expr) :
    subst x v (litBody lty kes σ) = litBody lty kes (fun j => subst x v (σ j)) := by
  simp [litBody, subst, substKeyedElements_kesσ]

theorem kesσ_congr : ∀ (kes : List (Option GoString × go.GoType)) (i : Nat) (σ σ' : Nat → Expr),
    (∀ j, i ≤ j → j < i + kes.length → σ j = σ' j) → kesσ kes i σ = kesσ kes i σ'
  | [], _, _, _, _ => rfl
  | (k, t) :: r, i, σ, σ', h => by
    simp only [kesσ]
    rw [h i (Nat.le_refl _) (by simp), kesσ_congr r (i + 1) σ σ' fun j h1 h2 => h j (by omega)
      (by simp at h2 ⊢; omega)]

mutual
/-- **The store is closed**: no substitution changes it. -/
theorem subst_storeTree (x : String) (v : val) : ∀ t : VTree, subst x v (storeTree t) = storeTree t
  | .leaf _ => by simp [storeTree, subst]
  | .ptr ty t => by simp [storeTree, subst, subst_storeTree x v t]
  | .slice ty ts => by
    simp only [storeTree]
    exact subst_storeTrees_body x v ts _ _ (by simp [sliceKes])
  | .strct ty fs ts => by
    simp only [storeTree]
    exact subst_storeTrees_body x v ts _ _ (by simp [strctKes]; omega)

/-- Through the `let`s of `storeTrees ts 0`, to a body whose names are bound by them. -/
theorem subst_storeTrees_body (x : String) (v : val) (ts : List VTree) (lty : go.GoType)
    (kes : List (Option GoString × go.GoType)) (hk : kes.length ≤ ts.length) :
    subst x v (storeTrees ts 0 (litBody lty kes varσ)) = storeTrees ts 0 (litBody lty kes varσ) := by
  by_cases hx : ∃ j, j < ts.length ∧ x = vname j
  · obtain ⟨j, hj, rfl⟩ := hx
    exact subst_storeTrees_shadow (vname j) v ts 0 _ j (by omega) (by omega) rfl
  · have hne : ∀ j, 0 ≤ j → j < 0 + ts.length → x ≠ vname j := fun j _ hj hx' => hx ⟨j, by omega, hx'⟩
    rw [subst_storeTrees_thru x v ts 0 _ hne, subst_litBody]
    simp only [litBody]
    rw [kesσ_congr kes 0 _ varσ fun j _ hj => by
      simp only [varσ, subst]
      exact if_neg (fun h => hx ⟨j, by omega, h⟩)]

/-- A substitution of a name none of the `let`s binds goes through them (the trees are closed). -/
theorem subst_storeTrees_thru (x : String) (v : val) :
    ∀ (ts : List VTree) (i : Nat) (e : Expr), (∀ j, i ≤ j → j < i + ts.length → x ≠ vname j) →
      subst x v (storeTrees ts i e) = storeTrees ts i (subst x v e)
  | [], _, _, _ => by simp [storeTrees]
  | t :: ts, i, e, h => by
    have hi : x ≠ vname i := h i (Nat.le_refl _) (by simp)
    have hb : BNamed x ≠ BNamed (vname i) := fun hb => hi (by cases hb; rfl)
    simp only [storeTrees, Let, Lam, subst, subst_storeTree x v t]
    rw [if_pos (⟨by simp, hb⟩ : BNamed x ≠ BAnon ∧ BNamed x ≠ BNamed (vname i)), subst_storeTrees_thru x v ts (i + 1) e
      (fun j h1 h2 => h j (by omega) (by simp at h2 ⊢; omega))]

/-- A substitution of a name one of the `let`s binds stops there (the trees are closed). -/
theorem subst_storeTrees_shadow (x : String) (v : val) :
    ∀ (ts : List VTree) (i : Nat) (e : Expr) (j : Nat), i ≤ j → j < i + ts.length →
      x = vname j → subst x v (storeTrees ts i e) = storeTrees ts i e
  | [], _, _, _, _, h2, _ => by simp at h2; omega
  | t :: ts, i, e, j, h1, h2, hx => by
    simp only [storeTrees, Let, Lam, subst, subst_storeTree x v t]
    by_cases hij : i = j
    · subst hij; subst hx
      rw [if_neg (fun h => h.2 rfl)]
    · have hb : BNamed x ≠ BNamed (vname i) := fun hb => by
        cases hb; exact hij (vname_inj hx)
      rw [if_pos (⟨by simp, hb⟩ : BNamed x ≠ BAnon ∧ BNamed x ≠ BNamed (vname i)), subst_storeTrees_shadow x v ts (i + 1) e j (by omega)
        (by simp at h2 ⊢; omega) hx]
end

end syntax_

/-! ## The store's WP, proved once -/

section wps
open Iris.ProgramLogic
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The elements bound to the values `vs`, the rest to their names. -/
def envσ (vs : List val) : Nat → Expr := fun j => if h : j < vs.length then Val vs[j] else Var (vname j)

theorem envσ_nil : envσ [] = varσ := by
  funext j; simp [envσ, varσ]

theorem subst_envσ (vs : List val) (v : val) :
    (fun j => subst (vname vs.length) v (envσ vs j)) = envσ (vs ++ [v]) := by
  funext j
  simp only [envσ, List.length_append, List.length_cons, List.length_nil]
  by_cases hj : j < vs.length
  · rw [dif_pos hj, dif_pos (by omega), List.getElem_append_left hj]; rfl
  · rw [dif_neg hj]
    by_cases hj' : j = vs.length
    · subst hj'
      rw [dif_pos (by omega)]
      simp [subst]
    · rw [dif_neg (by omega)]
      simp only [subst]
      rw [if_neg (fun h => hj' (vname_inj h).symm)]

mutual
/-- **What `storeTree t` needs** to end in `Φ`, node by node: a pointer node the allocation of its
tree's value, a literal node the literal of its trees' values (each not a panic). -/
def treeWp : VTree → (val → IProp GF) → IProp GF
  | .leaf v, Φ => Φ v
  | .ptr ty t, Φ => treeWp t (fun v => WP (App (Val (GoInstruction (GoAlloc ty))) (Val v)) {{ Φ }})
  | .slice ty ts, Φ => treeWpL ts []
      (fun vs => WP (litBody (go.SliceType ty) (sliceKes ty ts.length) (envσ vs)) {{ Φ }})
  | .strct ty fs ts, Φ => treeWpL ts []
      (fun vs => WP (litBody ty (strctKes fs ts.length) (envσ vs)) {{ Φ }})

/-- What the trees `ts` need, in order, their values appended to `acc`, to end in `Ψ`. -/
def treeWpL : List VTree → List val → (List val → IProp GF) → IProp GF
  | [], acc, Ψ => Ψ acc
  | t :: ts, acc, Ψ => treeWp t (fun v => iprop(⌜v.isPanic = false⌝ ∗ treeWpL ts (acc ++ [v]) Ψ))
end

mutual
/-- **The store's WP**, for every tree (proved once). -/
theorem storeTree_wp : ∀ (t : VTree) (Φ : val → IProp GF),
    treeWp t Φ ⊢ WP (storeTree t) {{ Φ }}
  | .leaf v, Φ => by
    simp only [treeWp, storeTree]
    exact wp_value'
  | .ptr ty t, Φ => by
    simp only [treeWp, storeTree]
    refine (storeTree_wp t _).trans ?_
    exact wp_bind (fill [EctxItem.AppRCtx (Val (GoInstruction (GoAlloc ty)))])
  | .slice ty ts, Φ => by
    simp only [treeWp, storeTree]
    have := storeTrees_wp ts [] (go.SliceType ty) (sliceKes ty ts.length) Φ
    rwa [envσ_nil] at this
  | .strct ty fs ts, Φ => by
    simp only [treeWp, storeTree]
    have := storeTrees_wp ts [] ty (strctKes fs ts.length) Φ
    rwa [envσ_nil] at this

/-- The `let`s of the trees `ts`, after those of `acc`'s. -/
theorem storeTrees_wp : ∀ (ts : List VTree) (acc : List val) (lty : go.GoType)
    (kes : List (Option GoString × go.GoType)) (Φ : val → IProp GF),
    treeWpL ts acc (fun vs => WP (litBody lty kes (envσ vs)) {{ Φ }}) ⊢
      WP (storeTrees ts acc.length (litBody lty kes (envσ acc))) {{ Φ }}
  | [], acc, lty, kes, Φ => by
    simp only [treeWpL, storeTrees]
    exact .rfl
  | t :: ts, acc, lty, kes, Φ => by
    simp only [treeWpL, storeTrees, Let, Lam]
    refine (storeTree_wp t _).trans (.trans ?_
      (wp_bind (fill [EctxItem.AppRCtx (Rec BAnon (BNamed (vname acc.length))
        (storeTrees ts (acc.length + 1) (litBody lty kes (envσ acc))))])))
    refine wp_mono fun v => ?_
    change _ ⊢ WP (App (Rec BAnon (BNamed (vname acc.length))
      (storeTrees ts (acc.length + 1) (litBody lty kes (envσ acc)))) (Val v)) {{ Φ }}
    iintro ⟨%Hv, H⟩
    have hrest := storeTrees_wp ts (acc ++ [v]) lty kes Φ
    have hsub : subst (vname acc.length) v
        (storeTrees ts (acc.length + 1) (litBody lty kes (envσ acc))) =
        storeTrees ts (acc ++ [v]).length (litBody lty kes (envσ (acc ++ [v]))) := by
      rw [subst_storeTrees_thru _ _ ts _ _ (fun j h1 _ h => by have := vname_inj h; omega),
        subst_litBody, subst_envσ]
      simp
    wp_pure
    wp_pure
    rw [hsub]
    iapply hrest $$ H
end

mutual
/-- `treeWp` is monotone in its postcondition. -/
theorem treeWp_mono : ∀ (t : VTree) (Φ Ψ : val → IProp GF), (∀ v, Φ v ⊢ Ψ v) →
    treeWp t Φ ⊢ treeWp t Ψ
  | .leaf v, _, _, h => by simp only [treeWp]; exact h v
  | .ptr _ t, _, _, h => by simp only [treeWp]; exact treeWp_mono t _ _ fun v => wp_mono h
  | .slice _ ts, _, _, h => by simp only [treeWp]; exact treeWpL_mono ts [] _ _ fun vs => wp_mono h
  | .strct _ _ ts, _, _, h => by simp only [treeWp]; exact treeWpL_mono ts [] _ _ fun vs => wp_mono h

theorem treeWpL_mono : ∀ (ts : List VTree) (acc : List val) (Ψ1 Ψ2 : List val → IProp GF),
    (∀ vs, Ψ1 vs ⊢ Ψ2 vs) → treeWpL ts acc Ψ1 ⊢ treeWpL ts acc Ψ2
  | [], acc, _, _, h => by simp only [treeWpL]; exact h acc
  | t :: ts, acc, _, _, h => by
    simp only [treeWpL]
    exact treeWp_mono t _ _ fun v => sep_mono_right (treeWpL_mono ts _ _ _ h)
end

/-- **The store's WP at `l`** (proved once). -/
theorem storeInto_wp (ty : go.GoType) (l : Loc) (t : VTree) (Φ : val → IProp GF) :
    treeWp t (fun v => iprop(⌜v.isPanic = false⌝ ∗
      WP (App (Val (GoInstruction (GoStore ty))) (Val (PairV #l v))) {{ Φ }})) ⊢
    WP (storeInto ty l t) {{ Φ }} := by
  refine (storeTree_wp t _).trans (.trans ?_ (wp_bind (fill [EctxItem.PairRCtx #l (isPanic_intoVal l),
    EctxItem.AppRCtx (Val (GoInstruction (GoStore ty)))])))
  refine wp_mono fun v => ?_
  change _ ⊢ WP (App (Val (GoInstruction (GoStore ty))) (Pair (Val #l) (Val v))) {{ Φ }}
  iintro ⟨%Hv, H⟩
  wp_pure
  iexact H

/-- **A typed pointer node**: the allocation of a `V` at `ty`. -/
theorem treeWp_ptr {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V ty]
    (t : VTree) (Φ : val → IProp GF) :
    treeWp t (fun v => iprop(∃ x : V, ⌜v = #x⌝ ∗ ∀ p : Loc, p ↦ x -∗ Φ #p)) ⊢ treeWp (.ptr ty t) Φ := by
  simp only [treeWp]
  refine treeWp_mono t _ _ fun v => ?_
  iintro ⟨%x, %Hx, H⟩
  subst Hx
  wp_alloc p as Hp
  iapply H $$ Hp

/-- **The typed store** of a `V` at `ty`. -/
theorem storeInto_wp_typed {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V ty] (l : Loc) (x0 : V) (t : VTree) (Φ : val → IProp GF) :
    treeWp t (fun v => iprop(∃ x : V, ⌜v = #x⌝ ∗ l ↦ x0 ∗ (l ↦ x -∗ Φ #()))) ⊢
    WP (storeInto ty l t) {{ Φ }} := by
  refine .trans ?_ (storeInto_wp ty l t Φ)
  refine treeWp_mono t _ _ fun v => ?_
  iintro ⟨%x, %Hx, Hl, H⟩
  subst Hx
  isplitr
  · ipureintro; exact isPanic_intoVal x
  wp_apply_core (IntoValTyped.wp_store (t := ty) l x0 x) $$ [$Hl]
  iintro Hl
  iapply H $$ Hl

/-- Leaves pass their values on. -/
theorem treeWpL_leaves {V : Type} (xs : List V) :
    ∀ (acc : List val) (Ψ : List val → IProp GF),
    Ψ (acc ++ xs.map fun x => #x) ⊢ treeWpL (xs.map fun x => VTree.leaf #x) acc Ψ := by
  induction xs with
  | nil => intro acc Ψ; simp only [List.map_nil, List.append_nil, treeWpL]; exact .rfl
  | cons x xs ih =>
    intro acc Ψ
    simp only [List.map_cons, treeWpL, treeWp]
    rw [show acc ++ #x :: List.map (fun x => #x) xs = (acc ++ [(#x)]) ++ List.map (fun x => #x) xs by simp]
    iintro H
    isplitr
    · ipureintro; exact isPanic_intoVal x
    iapply ih $$ H

/-- A slice literal's elements of the values `xs`. -/
theorem kesσ_vals {V : Type} (ty : go.GoType) (xs : List V) : ∀ (pre : List val),
    kesσ (List.replicate xs.length (none, ty)) pre.length (envσ (pre ++ xs.map fun x => #x)) =
      xs.map (arrayLitKE ty) := by
  induction xs with
  | nil => intro pre; simp [kesσ]
  | cons x xs ih =>
    intro pre
    simp only [List.length_cons, List.replicate_succ, kesσ, List.map_cons]
    have h := ih (pre ++ [(#x)])
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
      List.singleton_append] at h
    rw [h]
    simp [envσ, arrayLitKE]

theorem arrayLiteralSize_vals {V : Type} (ty : go.GoType) (xs : List V) :
    go.arrayLiteralSize (xs.map (arrayLitKE ty)) = xs.length := by
  have h : ∀ (f : Int × Int → keyed_element → Int × Int),
      (∀ (a b : Int) (y : V), f (a, b) (arrayLitKE ty y) = (a + 1, b)) →
      ∀ (ys : List V) (a b : Int), List.foldl f (a, b) (ys.map (arrayLitKE ty)) = (a + ys.length, b) := by
    intro f hf ys
    induction ys with
    | nil => intro a b; simp
    | cons y ys ih =>
      intro a b
      simp only [List.map_cons, List.foldl_cons, hf, List.length_cons]
      rw [ih]; congr 1; push_cast; omega
  unfold go.arrayLiteralSize
  rw [h _ (fun a b y => rfl) xs 0 0]
  simp

set_option goose.wp.unfoldSliceLiterals true in
/-- **A slice node of values**: a fresh slice holding `xs` (a literal of `2^63` elements or more
exits angelically, as Go cannot build one). -/
theorem treeWp_slice_vals {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V ty] (xs : List V) (Φ : val → IProp GF) :
    (∀ sl : GoSlice, ⌜xs.length < 2 ^ 63⌝ -∗ sl ↦* xs -∗ ownSliceCap V sl (DFrac.own 1) -∗ Φ #sl) ⊢
      treeWp (.slice ty (xs.map fun x => VTree.leaf #x)) Φ := by
  simp only [treeWp]
  refine .trans ?_ (treeWpL_leaves xs [] _)
  simp only [List.nil_append, List.length_map, litBody]
  have hk := kesσ_vals ty xs []
  simp only [List.length_nil, List.nil_append] at hk
  rw [sliceKes, hk]
  iintro HΦ
  wp_pures
  rw [arrayLiteralSize_vals]
  by_cases hlen : (xs.length : Int) < 2 ^ 63
  · rw [ite_eq_left hlen]
    wp_pures
    wp_alloc_auto
    wp_pure
    wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.ArrayType _ ty)))) (Val (LiteralValueV _)))
    have hstep := (pure_wp_array_lit_full (G := hG.goose_globalGS) (L := hG.goose_localGS)
      (xs.length : Int) ty xs _ rfl (by simp) (by omega)).pure_wp_wp .NotStuck ⊤
      (fun v => WP (Seq (App (Val (GoInstruction (GoStore (go.ArrayType (xs.length : Int) ty))))
          (Pair (Val #tmp_ptr) (Val v)))
        (App (Val (GoInstruction (GoInstruction.Slice (go.ArrayType (xs.length : Int) ty))))
          (Pair (Pair (Val #tmp_ptr) (Val #(W64 0))) (Val #(W64 xs.length))))) {{ Φ }}) [] trivial
    simp only [fill, List.foldl] at hstep
    iapply hstep
    inext
    iintro -
    wp_auto
    have hn : sint.Z (W64 (xs.length : Int)) = xs.length := by word
    rw [ite_eq_left ⟨by decide, by rw [hn]; word, by rw [hn]; exact Int.le_refl _⟩]
    have hz : W64 (xs.length : Int) - W64 0 = W64 (xs.length : Int) := by word
    simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, hz]
    wp_pures
    ihave Hs := slice_array tmp_ptr _ (array.mk (xs.length : Int) xs) (by simp only; omega) $$ tmp
    ihave Hc := ownSliceCap_empty (V := V) (slice.mk tmp_ptr (W64 (xs.length : Int)) (W64 (xs.length : Int))) rfl (by simp only; word)
    iapply HΦ $$ %(slice.mk tmp_ptr (W64 (xs.length : Int)) (W64 (xs.length : Int))) %(by omega) Hs Hc
  · rw [ite_eq_right hlen]; iapply wp_AngelicExit

/-! ### Normalizing nodes: a scalar cell, a bytes field -/

/-- **A proto2 optional scalar's cell**: `nil` for the zero value (what decoding gives for an
absent field), else a fresh pointer to it. -/
def cellTree {V : Type} [ZeroVal V] (ty : go.GoType) (x : V) : VTree :=
  open Classical in if x = zero_val V then .leaf #(null : Loc) else .ptr ty (.leaf #x)

/-- **A `bytes` (or repeated scalar) field**: `nil` if empty (protobuf-go decodes an empty
`bytes` field as `nil`), else a fresh slice. -/
def bytesTree {V : Type} (ty : go.GoType) (xs : List V) : VTree :=
  open Classical in if xs = [] then .leaf #slice.nil else .slice ty (xs.map fun x => .leaf #x)

theorem treeWp_cell {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V ty] (x : V) (Φ : val → IProp GF) :
    (∀ p : Loc, (⌜p = null ∧ x = zero_val V⌝ ∨ p ↦ x) -∗ Φ #p) ⊢ treeWp (cellTree ty x) Φ := by
  unfold cellTree
  by_cases hx : x = zero_val V
  · rw [if_pos hx]
    simp only [treeWp]
    iintro H
    iapply H
    ileft; ipureintro; exact ⟨rfl, hx⟩
  · rw [if_neg hx]
    refine .trans ?_ (treeWp_ptr (.leaf #x) Φ)
    simp only [treeWp]
    iintro H
    iexists x
    isplitr
    · ipureintro; rfl
    iintro %p Hp
    iapply H
    iright; iexact Hp

theorem treeWp_bytes {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V ty] (xs : List V) (Φ : val → IProp GF) :
    (∀ sl : GoSlice, ⌜xs.length < 2 ^ 63 ∧ (xs = [] → sl = slice.nil)⌝ -∗ sl ↦* xs -∗
      ownSliceCap V sl (DFrac.own 1) -∗ Φ #sl) ⊢ treeWp (bytesTree ty xs) Φ := by
  unfold bytesTree
  by_cases hx : xs = []
  · rw [if_pos hx]
    subst hx
    simp only [treeWp]
    iintro H
    ihave Hs := ownSlice_nil (V := V) (GF := GF) (DFrac.own 1)
    ihave Hc := ownSliceCap_nil (V := V) (GF := GF)
    iapply H $$ %slice.nil %(by simp) Hs Hc
  · rw [if_neg hx]
    refine .trans ?_ (treeWp_slice_vals xs Φ)
    iintro H %sl %Hl Hs Hc
    iapply H $$ %sl %(⟨Hl, fun h => absurd h hx⟩ : xs.length < 2 ^ 63 ∧ (xs = [] → sl = slice.nil)) Hs Hc

end wps

end EtcdGrove
end Perennial
