/-
**`value`'s agreement laws, proved** (structured-merge-diff v7.0.0): two readings of the same
interface, view or field list hold the same value (`isIface_agree'`, `isMapV_agree`,
`isListV_agree`, `isFieldList_agree`). A defs-tier module: it unfolds the sealed predicates.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7
open ValuePure

/-! ## Pure: the keys of two sorted lists with the same lookups agree -/

theorem keys_ext {α β : Type} : ∀ (a : List (GoString × α)) (b : List (GoString × β)),
    keysSorted a = true → keysSorted b = true →
    (∀ m, (lookupKV m a).isSome = (lookupKV m b).isSome) → kvKeys a = kvKeys b
  | [], [], _, _, _ => rfl
  | [], (k, v) :: _, _, _, h => by have := h k; simp [lookupKV] at this
  | (k, v) :: _, [], _, _, h => by have := h k; simp [lookupKV] at this
  | (k, v) :: a', (k', v') :: b', ha, hb, h => by
      have hk : k = k' := by
        cases h1 : gsLt k k' with
        | true =>
          have := h k
          rw [lookupKV_below hb h1] at this
          simp [lookupKV] at this
        | false =>
          cases h2 : gsLt k' k with
          | true =>
            have := h k'
            rw [lookupKV_below ha h2] at this
            simp [lookupKV] at this
          | false => exact gsLt_total h1 h2
      subst hk
      have ih := keys_ext a' b' (keysSorted_tail ha) (keysSorted_tail hb) (fun m => by
        by_cases hm : m = k
        · subst hm; rw [lookupKV_head_none ha, lookupKV_head_none hb]; rfl
        · have := h m
          simpa [lookupKV, Ne.symm hm] using this)
      simp only [kvKeys, List.map_cons] at ih ⊢
      rw [ih]

/-- The dynamic type an interface holding a non-null `x` has. -/
def uvTy : UVal → go.GoType
  | .null => go.bool
  | .bool _ => go.bool
  | .int _ => go.int64
  | .str _ => go.string
  | .list _ => sliceIfaceTy
  | .map _ => mapStrIfaceTy

/-- `x`'s kind. -/
def uvTag : UVal → Nat
  | .null => 0
  | .bool _ => 1
  | .int _ => 2
  | .str _ => 3
  | .list _ => 4
  | .map _ => 5

theorem uvTy_inj (x y : UVal) (hx : x ≠ .null) (hy : y ≠ .null) (h : uvTy x = uvTy y) :
    uvTag x = uvTag y := by
  cases x <;> cases y <;> simp_all [uvTy, uvTag, go.bool, go.int64, go.string, sliceIfaceTy, mapStrIfaceTy]

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem isIface_shape (i : GoInterface) (x : UVal) :
    isIface (GF := GF) i x ⊢
      ⌜(x = .null ∧ i = interface.nil) ∨ (x ≠ .null ∧ ∃ v, i = interface.mkOk (uvTy x) v)⌝ := by
  cases x with
  | null => iunfold isIface; iintro %h; ipureintro; exact Or.inl ⟨rfl, h⟩
  | bool b => iunfold isIface; iintro %h; ipureintro; exact Or.inr ⟨by simp, _, h⟩
  | int n => iunfold isIface; iintro %h; ipureintro; exact Or.inr ⟨by simp, _, h⟩
  | str s => iunfold isIface; iintro %h; ipureintro; exact Or.inr ⟨by simp, _, h⟩
  | list vs =>
    iunfold isIface
    iintro ⟨%sl, %xs, %h, -⟩
    ipureintro; exact Or.inr ⟨by simp, _, h⟩
  | map kvs =>
    iunfold isIface
    iintro ⟨%m, %M, %h, -⟩
    ipureintro; exact Or.inr ⟨by simp, _, h⟩

theorem isIface_tag (i : GoInterface) (x y : UVal) :
    isIface (GF := GF) i x ∗ isIface i y ⊢ ⌜uvTag x = uvTag y⌝ := by
  iintro ⟨H1, H2⟩
  ihave %h1 := isIface_shape i x $$ H1
  ihave %h2 := isIface_shape i y $$ H2
  ipureintro
  rcases h1 with ⟨rfl, rfl⟩ | ⟨hx, v, rfl⟩ <;> rcases h2 with ⟨rfl, h⟩ | ⟨hy, w, h⟩
  · rfl
  · simp [interface.mkOk] at h
  · simp [interface.mkOk] at h
  · rw [interface_mkOk_inj] at h
    exact uvTy_inj x y hx hy h.1

mutual
theorem isIface_agree' : ∀ (i : GoInterface) (x y : UVal),
    isIface (GF := GF) i x ∗ isIface i y ⊢ ⌜x = y⌝
  | i, .null, y => by
    iintro ⟨H1, H2⟩
    ihave %ht := isIface_tag i .null y $$ [H1 H2]
    · iframe
    cases y <;> simp [uvTag] at ht
    ipureintro; rfl
  | i, .bool b, y => by
    iintro ⟨H1, H2⟩
    ihave %ht := isIface_tag i (.bool b) y $$ [H1 H2]
    · iframe
    cases y <;> simp [uvTag] at ht
    iunfold isIface at H1 H2
    icases H1 with %h1
    icases H2 with %h2
    rw [h1, interface_mkOk_inj, intoVal_eq_iff] at h2
    ipureintro; rw [h2.2]
  | i, .int n, y => by
    iintro ⟨H1, H2⟩
    ihave %ht := isIface_tag i (.int n) y $$ [H1 H2]
    · iframe
    cases y <;> simp [uvTag] at ht
    iunfold isIface at H1 H2
    icases H1 with %h1
    icases H2 with %h2
    rw [h1, interface_mkOk_inj, intoVal_eq_iff] at h2
    ipureintro; rw [h2.2]
  | i, .str s, y => by
    iintro ⟨H1, H2⟩
    ihave %ht := isIface_tag i (.str s) y $$ [H1 H2]
    · iframe
    cases y <;> simp [uvTag] at ht
    iunfold isIface at H1 H2
    icases H1 with %h1
    icases H2 with %h2
    rw [h1, interface_mkOk_inj, intoVal_eq_iff] at h2
    ipureintro; rw [h2.2]
  | i, .list vs, y => by
    iintro ⟨H1, H2⟩
    ihave %ht := isIface_tag i (.list vs) y $$ [H1 H2]
    · iframe
    cases y <;> simp [uvTag] at ht
    rename_i ws
    iunfold isIface at H1 H2
    icases H1 with ⟨%sl, %xs, %h1, Hs1, HL1⟩
    icases H2 with ⟨%sl', %xs', %h2, Hs2, HL2⟩
    rw [h1, interface_mkOk_inj, intoVal_eq_iff] at h2
    obtain ⟨-, rfl⟩ := h2
    ihave %hx := ownSlice_agree _ _ _ _ _ $$ Hs1 Hs2
    subst hx
    ihave %h := isIfaceL_agree xs vs ws $$ [HL1 HL2]
    · iframe
    ipureintro; rw [h]
  | i, .map kvs, y => by
    iintro ⟨H1, H2⟩
    ihave %ht := isIface_tag i (.map kvs) y $$ [H1 H2]
    · iframe
    cases y <;> simp [uvTag] at ht
    rename_i kvs'
    iunfold isIface at H1 H2
    icases H1 with ⟨%m, %M, %h1, Hm1, %Hk1, HM1⟩
    icases H2 with ⟨%m', %M', %h2, Hm2, %Hk2, HM2⟩
    rw [h1, interface_mkOk_inj, intoVal_eq_iff] at h2
    obtain ⟨-, rfl⟩ := h2
    ihave %hM := ownMap_agree m _ _ M M' $$ [Hm1 Hm2]
    · iframe
    subst hM
    have hkeys : kvKeys kvs = kvKeys kvs' :=
      keys_ext kvs kvs' Hk1.1 Hk2.1 (fun k => by rw [← Hk1.2, ← Hk2.2])
    ihave %h := isIfaceM_agree M kvs kvs' hkeys $$ [HM1 HM2]
    · iframe
    ipureintro; rw [h]
theorem isIfaceL_agree : ∀ (xs : List GoInterface) (vs ws : List UVal),
    isIfaceL (GF := GF) xs vs ∗ isIfaceL xs ws ⊢ ⌜vs = ws⌝
  | [], [], [] => by iintro -; ipureintro; rfl
  | x :: xs, v :: vs, w :: ws => by
    iintro ⟨H1, H2⟩
    iunfold isIfaceL at H1 H2
    icases H1 with ⟨Hx1, H1⟩
    icases H2 with ⟨Hx2, H2⟩
    ihave %h1 := isIface_agree' x v w $$ [Hx1 Hx2]
    · iframe
    ihave %h2 := isIfaceL_agree xs vs ws $$ [H1 H2]
    · iframe
    ipureintro; rw [h1, h2]
  | [], _ :: _, _ => by iintro ⟨H, -⟩; iunfold isIfaceL at H; iexfalso; iexact H
  | _ :: _, [], _ => by iintro ⟨H, -⟩; iunfold isIfaceL at H; iexfalso; iexact H
  | [], [], _ :: _ => by iintro ⟨-, H⟩; iunfold isIfaceL at H; iexfalso; iexact H
  | _ :: _, _ :: _, [] => by iintro ⟨-, H⟩; iunfold isIfaceL at H; iexfalso; iexact H
theorem isIfaceM_agree : ∀ (M : GMap GoString GoInterface) (kvs kvs' : List (GoString × UVal)),
    kvKeys kvs = kvKeys kvs' → isIfaceM (GF := GF) M kvs ∗ isIfaceM M kvs' ⊢ ⌜kvs = kvs'⌝
  | M, [], [], _ => by iintro -; ipureintro; rfl
  | M, [], _ :: _, h => by simp [kvKeys] at h
  | M, _ :: _, [], h => by simp [kvKeys] at h
  | M, (k, v) :: kvs, (k', v') :: kvs', h => by
    simp only [kvKeys, List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    iintro ⟨H1, H2⟩
    iunfold isIfaceM at H1 H2
    icases H1 with ⟨%x, %hx, Hx, H1⟩
    icases H2 with ⟨%x', %hx', Hx', H2⟩
    rw [hx] at hx'
    cases hx'
    ihave %h1 := isIface_agree' x v v' $$ [Hx Hx']
    · iframe
    ihave %h2 := isIfaceM_agree M kvs kvs' h $$ [H1 H2]
    · iframe
    ipureintro; rw [h1, h2]
end

end lemmas

/-! ## The laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem isMapV_agree_law_holds : isMapV_agree.law (GF := GF) := fun m a b => by
  iintro ⟨H1, H2⟩
  iunfold isMapV at H1 H2
  icases H1 with ⟨%gm, %h1, Hi1⟩
  icases H2 with ⟨%gm', %h2, Hi2⟩
  rw [h1, interface_mkOk_inj, intoVal_eq_iff] at h2
  obtain ⟨-, rfl⟩ := h2
  ihave %h := isIface_agree' _ _ _ $$ [Hi1 Hi2]
  · iframe
  ipureintro; cases h; rfl

theorem isListV_agree_law_holds : isListV_agree.law (GF := GF) := fun l a b => by
  iintro ⟨H1, H2⟩
  iunfold isListV at H1 H2
  icases H1 with ⟨%sl, Hi1, (%h1 | ⟨%p, %h1, Hp1⟩)⟩ <;>
    icases H2 with ⟨%sl', Hi2, (%h2 | ⟨%p', %h2, Hp2⟩)⟩ <;>
    rw [h1, interface_mkOk_inj] at h2
  · rw [intoVal_eq_iff] at h2
    obtain ⟨-, rfl⟩ := h2
    ihave %h := isIface_agree' _ _ _ $$ [Hi1 Hi2]
    · iframe
    ipureintro; cases h; rfl
  · simp [value.listUnstructured.ty] at h2
  · simp [value.listUnstructured.ty] at h2
  · rw [intoVal_eq_iff] at h2
    obtain ⟨-, rfl⟩ := h2
    ihave %hs := typedPointsto_agree_wand _ _ _ _ _ $$ Hp1 Hp2
    subst hs
    ihave %h := isIface_agree' _ _ _ $$ [Hi1 Hi2]
    · iframe
    ipureintro; cases h; rfl

theorem isFieldsL_agree : ∀ (fs : List value.Field) (a b : FieldList),
    isFieldsL (GF := GF) fs a ∗ isFieldsL fs b ⊢ ⌜a = b⌝
  | [], [], [] => by iintro -; ipureintro; rfl
  | f :: fs, (n, x) :: a, (n', x') :: b => by
    iintro ⟨H1, H2⟩
    iunfold isFieldsL at H1 H2
    icases H1 with ⟨%hn, Hv1, H1⟩
    icases H2 with ⟨%hn', Hv2, H2⟩
    unfold isVal; iunfold isValF at Hv1 Hv2
    icases Hv1 with ⟨%p, %i, %hp, Hp, Hi⟩
    icases Hv2 with ⟨%p', %i', %hp', Hp', Hi'⟩
    rw [hp, interface_mkOk_inj, intoVal_eq_iff] at hp'
    obtain ⟨-, rfl⟩ := hp'
    ihave %hi := typedPointsto_agree_wand _ _ _ _ _ $$ Hp Hp'
    cases hi
    ihave %hx := isIface_agree' _ _ _ $$ [Hi Hi']
    · iframe
    ihave %h := isFieldsL_agree fs a b $$ [H1 H2]
    · iframe
    ipureintro; rw [← hn, ← hn', hx, h]
  | [], _ :: _, _ => by iintro ⟨H, -⟩; iunfold isFieldsL at H; iexfalso; iexact H
  | _ :: _, [], _ => by iintro ⟨H, -⟩; iunfold isFieldsL at H; iexfalso; iexact H
  | [], [], _ :: _ => by iintro ⟨-, H⟩; iunfold isFieldsL at H; iexfalso; iexact H
  | _ :: _, _ :: _, [] => by iintro ⟨-, H⟩; iunfold isFieldsL at H; iexfalso; iexact H

theorem isFieldList_agree_law_holds : isFieldList_agree.law (GF := GF) := fun s a b => by
  iintro ⟨H1, H2⟩
  iunfold isFieldList at H1 H2
  icases H1 with ⟨%fs, Hs1, H1⟩
  icases H2 with ⟨%fs', Hs2, H2⟩
  ihave %hf := ownSlice_agree _ _ _ _ _ $$ Hs1 Hs2
  subst hf
  iapply isFieldsL_agree fs a b
  iframe

end laws

end smd
end EtcdGrove
end Perennial
