/-
**Persistence instances of the merge walker's vocabulary** (`Walkers.lean`): what the merging and
compare walkers' proofs keep in the intuitionistic context.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.WalkerLaws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

instance ruleKeepRHSOk_pers (f : GoFunc) : Persistent (ruleKeepRHSOk (GF := GF) f) := by
  unfold ruleKeepRHSOk; infer_instance

instance outRep_pers (o : Loc) : (x : Option UVal) → Persistent (outRep (GF := GF) o x)
  | none => by unfold outRep; infer_instance
  | some _ => by unfold outRep; infer_instance

instance isSetO_pers (p : Loc) : (o : Option PathSet) → Persistent (isSetO (GF := GF) p o)
  | none => by unfold isSetO; infer_instance
  | some _ => by unfold isSetO; infer_instance

/-- A set's pointer is not nil (its struct is allocated). -/
theorem trieRep_not_null (p : Loc) (t : Trie) : trieRep (GF := GF) p t ⊢ ⌜p ≠ null⌝ := by
  rcases t with ⟨ms, cs⟩
  unfold trieRep
  iintro ⟨%v, %es, %ns, Hp, -⟩
  iapply typedPointsto_not_null _ _ _ $$ Hp

theorem isSet_not_null (p : Loc) (S : PathSet) : isSet (GF := GF) p S ⊢ ⌜p ≠ null⌝ := by
  unfold isSet
  iintro ⟨%t, -, Ht⟩
  iapply trieRep_not_null $$ Ht

/-- A side is nil exactly when absent. -/
theorem isValO_nil (v : value.Value) (dq : DFrac) (o : Option UVal) :
    isValO (GF := GF) v dq o ⊢ isValO v dq o ∗ ⌜v = interface.nil ↔ o = none⌝ := by
  cases o with
  | none =>
    unfold isValO
    iintro %H
    isplitl; · ipureintro; exact H
    ipureintro; simp [H]
  | some x =>
    unfold isValO isValF
    iintro ⟨%p, %i, %Hv, Hp, Hi⟩
    isplitl
    · iexists p, i; iframe; ipureintro; exact Hv
    ipureintro
    subst Hv
    simp only [reduceCtorEq]

/-- A present side is a `*valueUnstructured`. -/
theorem isValO_some (v : value.Value) (dq : DFrac) (x : UVal) :
    isValO (GF := GF) v dq (some x) ⊢ isValO v dq (some x) ∗
      ⌜∃ p : Loc, v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p⌝ := by
  unfold isValO isValF
  iintro ⟨%p, %i, %Hv, Hp, Hi⟩
  isplitl
  · iexists p, i; iframe; ipureintro; exact Hv
  ipureintro; exact ⟨p, Hv⟩

/-- No errors: the nil slice. -/
theorem errsIff_nil (ok : Prop) (h : ok) : ⊢ errsIff (GF := GF) slice.nil ok := by
  unfold errsIff ownErrs
  iexists []
  isplitl
  · isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  · ipureintro; exact ⟨fun _ => h, fun _ => rfl⟩

theorem noErrs_nil : ⊢ noErrs (GF := GF) slice.nil := by
  unfold noErrs ownErrs
  isplitl
  · iapply ownSlice_nil
  · iapply ownSliceCap_nil

/-- An empty errors slice has length 0. -/
theorem noErrs_len (s : GoSlice) : noErrs (GF := GF) s ⊢ ⌜sint.Z s.len = 0⌝ := by
  unfold noErrs ownErrs
  iintro ⟨Hs, _⟩
  ihave %H := ownSlice_len _ _ _ $$ Hs
  ipureintro
  obtain ⟨h1, h2⟩ := H
  simp only [List.length_nil] at h1
  word

/-- Dropping a slice's last element into its capacity (`s[:len(s)-1]`). -/
theorem ownSlice_pop {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (sl : GoSlice) (ws' : List V) (x : V) :
    (sl ↦* (ws' ++ [x]) ∗ ownSliceCap V sl (DFrac.own 1) : IProp GF) ⊢
      slice.slice sl V (W64 0) (sl.len - W64 1) ↦* ws' ∗
      ownSliceCap V (slice.slice sl V (W64 0) (sl.len - W64 1)) (DFrac.own 1) := by
  iintro ⟨H, Hc⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ H
  ihave %Hwf := ownSlice_wf _ _ _ $$ H
  simp only [List.length_append, List.length_singleton] at Hlen
  have e := slice_slice_trivial (V := V) sl
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
      sint.Z (sl.len - W64 1) ≤ sint.Z sl.len := by word
  ihave H := (show (sl ↦* (ws' ++ [x]) : IProp GF) ⊢ slice.slice sl V (W64 0) sl.len ↦* (ws' ++ [x]) by
    rw [← e]) $$ H
  icases (ownSlice_split (sl.len - W64 1) sl (DFrac.own 1) (ws' ++ [x]) (W64 0) sl.len hb).1 $$ H
    with ⟨H1, H2⟩
  have h1 : sint.nat (sl.len - W64 1) - sint.nat (W64 0) = ws'.length := by word
  rw [h1, List.take_left, List.drop_left]
  iframe H1
  iapply ownSlice_slice_absorb_capacity sl [x] (W64 0) (sl.len - W64 1) hb
  iframe

/-- A walker's path slice: its length is the path's. -/
theorem ownPath_len (s : fieldpath.Path) (p : Path) :
    ownPath (GF := GF) s p ⊢ ownPath s p ∗
      ⌜sint.nat s.len = p.length ∧ 0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap⌝ := by
  unfold ownPath isPathF
  iintro ⟨⟨%es, Hes, Hpes⟩, Hcap⟩
  ihave %Hl := isPEs_length_law_holds _ _ $$ Hpes
  ihave %Hlen := ownSlice_len _ _ _ $$ Hes
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hes
  isplitl
  · iframe
  · ipureintro; exact ⟨by omega, Hwf.1, Hwf.2⟩

/-- Truncating a walker's path by its last element (`finishDescent`'s `w2.path[:len(w2.path)-1]`). -/
theorem ownPath_pop (s : fieldpath.Path) (p : Path) (pe : PE) :
    ownPath (GF := GF) s (p ++ [pe]) ⊢
      ownPath (slice.slice s fieldpath.PathElement (W64 0) (s.len - W64 1)) p := by
  unfold ownPath isPathF
  iintro ⟨⟨%es, Hes, Hpes⟩, Hcap⟩
  ihave %Hl := isPEs_length_law_holds _ _ $$ Hpes
  simp only [List.length_append, List.length_singleton] at Hl
  have hes : es = es.take p.length ++ es.drop p.length := (List.take_append_drop _ _).symm
  have hd : (es.drop p.length).length = 1 := by simp; omega
  obtain ⟨e, he⟩ : ∃ e, es.drop p.length = [e] := by
    match h : es.drop p.length, hd with
    | [e], _ => exact ⟨e, rfl⟩
  rw [he] at hes
  rw [hes]
  rw [hes] at Hl
  icases (isPEs_app_law_holds (es.take p.length) [e] p [pe] (by simp at Hl ⊢; omega)).1 $$ Hpes
    with ⟨Hp1, -⟩
  icases ownSlice_pop s (es.take p.length) e $$ [$Hes $Hcap] with ⟨Hes, Hcap⟩
  iframe

/-- Calling `ruleKeepRHS`'s closure (the persistent spec read at one call). -/
theorem ruleKeepRHSOk_call (f : GoFunc) (w : Loc) (v : typed.mergingWalker) (dql dqr : DFrac)
    (l r : Option UVal) :
    ruleKeepRHSOk (GF := GF) f ⊢
    {{ w ↦ v ∗ isValO v.lhs' dql l ∗ isValO v.rhs' dqr r ∗ ⌜l.isSome ∨ r.isSome⌝ }}
      (App (Val #f) (Val #w))
    {{ RET #(); ∃ o : Loc, w ↦ { v with out' := o } ∗ outRep o (leafM l r) ∗
        isValO v.lhs' dql l ∗ isValO v.rhs' dqr r }} := by
  unfold ruleKeepRHSOk
  iintro #H
  iapply H

end laws

end smd
end EtcdGrove
end Perennial
