/-
**`value`'s laws, proved** (structured-merge-diff v7.0.0): the laws stated in `value/Objects.lean`
(`<X>.law`, proved as `<X>_law_holds`) and the lemmas on `value`'s sealed representation that the
package's own proofs use (persistence instances, the shape of an interface). A defs-tier module:
it unfolds the sealed predicates (`import all` of the package's own modules).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsPure
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

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## Persistence -/

mutual
theorem isIface_pers : ∀ (i : GoInterface) (x : UVal), Persistent (isIface (GF := GF) i x)
  | i, .null => by unfold isIface; infer_instance
  | i, .bool _ => by unfold isIface; infer_instance
  | i, .int _ => by unfold isIface; infer_instance
  | i, .str _ => by unfold isIface; infer_instance
  | i, .list vs => by
    have := fun xs => isIfaceL_pers xs vs
    unfold isIface; infer_instance
  | i, .map kvs => by
    have := fun M => isIfaceM_pers M kvs
    unfold isIface; infer_instance
theorem isIfaceL_pers : ∀ (xs : List GoInterface) (vs : List UVal),
    Persistent (isIfaceL (GF := GF) xs vs)
  | [], [] => by unfold isIfaceL; infer_instance
  | x :: xs, v :: vs => by
    have := isIface_pers x v
    have := isIfaceL_pers xs vs
    unfold isIfaceL; infer_instance
  | [], _ :: _ => by unfold isIfaceL; infer_instance
  | _ :: _, [] => by unfold isIfaceL; infer_instance
theorem isIfaceM_pers : ∀ (M : GMap GoString GoInterface) (kvs : List (GoString × UVal)),
    Persistent (isIfaceM (GF := GF) M kvs)
  | M, [] => by unfold isIfaceM; infer_instance
  | M, (k, v) :: kvs => by
    have := fun x => isIface_pers x v
    have := isIfaceM_pers M kvs
    unfold isIfaceM; infer_instance
end

attribute [instance] isIface_pers isIfaceL_pers isIfaceM_pers

instance isListV_pers (l : value.List') (vs : List UVal) : Persistent (isListV (GF := GF) l vs) := by
  unfold isListV; infer_instance
instance isMapV_pers (m : value.Map) (kvs : List (GoString × UVal)) :
    Persistent (isMapV (GF := GF) m kvs) := by
  unfold isMapV; infer_instance
instance isMapO_pers (m : value.Map) (o : Option (List (GoString × UVal))) :
    Persistent (isMapO (GF := GF) m o) := by
  cases o <;> unfold isMapO <;> infer_instance

/-! ## The package's named types are distinct -/

theorem emptyRange_ne_listUnstructuredRange :
    value.emptyRange.ty ≠ value.listUnstructuredRange.ty := by
  simp [value.emptyRange.ty, value.listUnstructuredRange.ty]

/-! ## The package's globals -/

theorem valuePkg_globals :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ⊢
      ∃ p q : Loc, globalAddr value.HeapAllocator ↦□ p ∗ globalAddr value.EmptyRange ↦□ q := by
  iintro #Hpkg
  ihave H := isPkgInit_access $$ Hpkg
  iexact H

/-! ## Wrappers -/

/-- The wrapper type. -/
abbrev vuPtrTy : go.GoType := go.GoType.PointerType value.valueUnstructured.ty

theorem isValF_intro (p : Loc) (dq : DFrac) (i : GoInterface) (x : UVal) :
    p ↦{dq} value.valueUnstructured.mk i ∗ isIface (GF := GF) i x ⊢
      isValF (interface.mkOk vuPtrTy #p) dq x := by
  iintro ⟨Hp, Hi⟩
  iunfold isValF
  iexists p, i
  iframe
  ipureintro
  rfl

theorem isValF_elim (p : Loc) (dq : DFrac) (x : UVal) :
    isValF (GF := GF) (interface.mkOk vuPtrTy #p) dq x ⊢
      ∃ i, p ↦{dq} value.valueUnstructured.mk i ∗ isIface (GF := GF) i x := by
  iintro Hv
  iunfold isValF at Hv
  icases Hv with ⟨%p', %i, %Heq, Hp, Hi⟩
  obtain rfl : p = p' := by simpa [intoVal_eq_iff] using Heq
  iexists i
  iframe

/-! ## Interfaces' shapes, the views' introduction -/

theorem isIface_list_shape (i : GoInterface) (vs : List UVal) :
    isIface (GF := GF) i (.list vs) ⊢ ⌜∃ sl : GoSlice, i = interface.mkOk sliceIfaceTy #sl⌝ := by
  iintro Hi
  iunfold isIface at Hi
  icases Hi with ⟨%sl, %xs, %Heq, -⟩
  ipureintro
  exact ⟨sl, Heq⟩

theorem isIface_map_shape (i : GoInterface) (kvs : List (GoString × UVal)) :
    isIface (GF := GF) i (.map kvs) ⊢ ⌜∃ m : GoMap, i = interface.mkOk mapStrIfaceTy #m⌝ := by
  iintro Hi
  iunfold isIface at Hi
  icases Hi with ⟨%m, %M, %Heq, -⟩
  ipureintro
  exact ⟨m, Heq⟩

theorem isListV_intro (sl : GoSlice) (vs : List UVal) :
    isIface (GF := GF) (interface.mkOk sliceIfaceTy #sl) (.list vs) ⊢
      isListV (interface.mkOk value.listUnstructured.ty #sl) vs := by
  iintro Hi
  iunfold isListV
  iexists sl
  iframe
  ileft
  ipureintro
  rfl

theorem isMapV_intro (gm : GoMap) (kvs : List (GoString × UVal)) :
    isIface (GF := GF) (interface.mkOk mapStrIfaceTy #gm) (.map kvs) ⊢
      isMapV (interface.mkOk value.mapUnstructuredString.ty #gm) kvs := by
  iintro Hi
  iunfold isMapV
  iexists gm
  iframe
  ipureintro
  rfl

/-! ## Allocators -/

theorem isAlloc_heap_intro (p : Loc) :
    ⊢ isAlloc (GF := GF) (interface.mkOk (go.GoType.PointerType value.heapAllocator.ty) #p) := by
  iunfold isAlloc
  ileft
  iexists p
  ipureintro
  rfl

/-! ## Maps -/

theorem isIface_map_val (gm : GoMap) (kvs : List (GoString × UVal)) :
    isIface (GF := GF) (interface.mkOk mapStrIfaceTy #gm) (.map kvs) ⊢
      ∃ M : GMap GoString GoInterface, gm ↦$□ M ∗
        ⌜keysSorted kvs = true ∧ ∀ k, (M !! k).isSome = (lookupKV k kvs).isSome⌝ ∗
        isIfaceM (GF := GF) M kvs := by
  iintro Hi
  iunfold isIface at Hi
  icases Hi with ⟨%gm', %M, %Heq, Hm, %Hk, HM⟩
  simp [intoVal_eq_iff] at Heq
  subst Heq
  iexists M
  iframe
  ipureintro
  exact Hk

theorem isMapV_val (gm : GoMap) (kvs : List (GoString × UVal)) :
    isMapV (GF := GF) (interface.mkOk value.mapUnstructuredString.ty #gm) kvs ⊢
      isIface (GF := GF) (interface.mkOk mapStrIfaceTy #gm) (.map kvs) := by
  iintro Hm
  iunfold isMapV at Hm
  icases Hm with ⟨%gm', %Heq, Hi⟩
  simp [intoVal_eq_iff] at Heq
  subst Heq
  iexact Hi

theorem isIfaceM_lookup (M : GMap GoString GoInterface) (k : GoString) (x : UVal) :
    ∀ (kvs : List (GoString × UVal)), lookupKV k kvs = some x →
    isIfaceM (GF := GF) M kvs ⊢ ∃ i, ⌜M !! k = some i⌝ ∗ isIface (GF := GF) i x
  | [], h => by simp [lookupKV] at h
  | (k', v') :: rest, h => by
    iintro H
    iunfold isIfaceM at H
    icases H with ⟨%i, %Hi, Hv, H⟩
    unfold lookupKV at h
    by_cases hk : k' = k
    · subst hk
      simp at h; subst h
      iexists i; iframe; ipureintro; exact Hi
    · simp only [hk, ite_false] at h
      iapply isIfaceM_lookup M k x rest h
      iexact H

theorem map_size_kvs (M : GMap GoString GoInterface) (kvs : List (GoString × UVal))
    (hs : keysSorted kvs = true) (hk : ∀ k, (M !! k).isSome = (lookupKV k kvs).isSome) :
    GMap.size M = kvs.length := by
  rw [GMap.size_eq_length M (kvKeys kvs) (ValuePure.keysSorted_nodup kvs hs)]
  · simp [kvKeys]
  · intro k
    rw [← ValuePure.lookupKV_isSome_iff, hk]

/-! ## Ranges -/

theorem ownRange_intro (q : Loc) (sl : GoSlice) (w : Loc) (iw : w64) (vs : List UVal) (i : Int)
    (hi : iw.toInt = i) :
    q ↦ value.listUnstructuredRange.mk sl w iw ∗
      isIface (GF := GF) (interface.mkOk sliceIfaceTy #sl) (.list vs) ∗ wrapperOwn (GF := GF) w ⊢
      ownRange (GF := GF) (interface.mkOk (go.GoType.PointerType value.listUnstructuredRange.ty) #q) vs
        i := by
  iintro ⟨Hq, Hi, Hw⟩
  iunfold ownRange
  iright
  iexists q, sl, w, iw
  iframe
  ipureintro
  exact ⟨rfl, hi⟩

/-! ## Lists -/

theorem isIfaceL_length (xs : List GoInterface) (vs : List UVal) :
    isIfaceL (GF := GF) xs vs ⊢ ⌜xs.length = vs.length⌝ := by
  induction vs generalizing xs with
  | nil => cases xs <;> simp [isIfaceL]
  | cons v vs ih =>
    cases xs with
    | nil => simp [isIfaceL]
    | cons x xs =>
      iintro H
      iunfold isIfaceL at H
      icases H with ⟨-, H⟩
      ihave %h := ih xs $$ H
      ipureintro
      simp [h]

theorem isIfaceL_lookup (xs : List GoInterface) (vs : List UVal) (k : Nat) (x : UVal)
    (hk : vs[k]? = some x) :
    isIfaceL (GF := GF) xs vs ⊢ ∃ i, ⌜xs[k]? = some i⌝ ∗ isIface (GF := GF) i x := by
  induction vs generalizing xs k with
  | nil => simp at hk
  | cons v vs ih =>
    cases xs with
    | nil => simp [isIfaceL]; exact false_elim
    | cons y ys =>
      iintro H
      iunfold isIfaceL at H
      icases H with ⟨Hy, H⟩
      cases k with
      | zero =>
        simp at hk; subst hk
        iexists y; iframe; ipureintro; rfl
      | succ k =>
        simp at hk
        simp only [List.getElem?_cons_succ]
        iapply ih ys k hk
        iexact H

theorem isListV_val (l : GoSlice) (vs : List UVal) :
    isListV (GF := GF) (interface.mkOk value.listUnstructured.ty #l) vs ⊢
      ∃ xs, l ↦*{DFrac.discard} xs ∗ isIfaceL (GF := GF) xs vs := by
  iintro Hl
  iunfold isListV at Hl
  icases Hl with ⟨%sl, Hi, (%Heq | ⟨%p, %Heq, -⟩)⟩
  · simp [intoVal_eq_iff] at Heq
    subst Heq
    iunfold isIface at Hi
    icases Hi with ⟨%sl', %xs, %Heq, Hs, HL⟩
    simp [intoVal_eq_iff] at Heq
    subst Heq
    iexists xs
    iframe
  · simp [value.listUnstructured.ty] at Heq

theorem isListV_iface (l : GoSlice) (vs : List UVal) :
    isListV (GF := GF) (interface.mkOk value.listUnstructured.ty #l) vs ⊢
      isIface (GF := GF) (interface.mkOk sliceIfaceTy #l) (.list vs) := by
  iintro Hl
  iunfold isListV at Hl
  icases Hl with ⟨%sl, Hi, (%Heq | ⟨%p, %Heq, -⟩)⟩
  · simp [intoVal_eq_iff] at Heq
    subst Heq
    iexact Hi
  · simp [value.listUnstructured.ty] at Heq

theorem isListV_ptr (p : Loc) (vs : List UVal) :
    isListV (GF := GF) (interface.mkOk (go.GoType.PointerType value.listUnstructured.ty) #p) vs ⊢
      ∃ sl : GoSlice, p ↦□ sl ∗ isListV (GF := GF) (interface.mkOk value.listUnstructured.ty #sl) vs := by
  iintro Hl
  iunfold isListV at Hl
  icases Hl with ⟨%sl, #Hi, (%Heq | ⟨%p', %Heq, #Hp⟩)⟩
  · simp [value.listUnstructured.ty] at Heq
  · simp [intoVal_eq_iff] at Heq
    subst Heq
    iexists sl
    isplitr
    · iexact Hp
    iunfold isListV
    iexists sl
    isplitr
    · iexact Hi
    ileft
    ipureintro
    rfl

end lemmas

/-! ## The stated laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem isMapV_persistent_law_holds : isMapV_persistent.law (GF := GF) := fun _ _ => by
  iintro #H; imodintro; iexact H
theorem isListV_persistent_law_holds : isListV_persistent.law (GF := GF) := fun _ _ => by
  iintro #H; imodintro; iexact H

theorem isAlloc_concrete_law_holds : isAlloc_concrete.law (GF := GF) := by
  intro a
  iintro Ha
  iunfold isAlloc at Ha
  icases Ha with (⟨%p, %h⟩ | ⟨%p, %fa, %h, #Hp, H1, H2⟩)
  · isplitl
    · iunfold isAlloc; ileft; iexists p; ipureintro; exact h
    · ileft; iexists p; ipureintro; exact h
  · isplitl
    · iunfold isAlloc; iright; iexists p, fa; iframe; isplitr
      · ipureintro; exact h
      · iexact Hp
    · iright; iexists p; ipureintro; exact h

end laws

end smd
end EtcdGrove
end Perennial
