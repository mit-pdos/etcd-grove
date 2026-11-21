/-
`merge.ConflictsFromManagers`:
proved (Prove, 2026-11-21): the `for range` over the read-only map keeps the conflicts appended so
far as the pairs of the managers visited (`pairVis`), each manager's by its set's `Iterate`
(appending a copy of each path); the list is the spec's existential one, in iteration order.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `fieldpath.versionedSet.Set`, `fieldpath.Set.Iterate`, `fieldpath.Path.Copy`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.ConflictsFromManagers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Path__Copy
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsM1

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : merge.Assumptions]

theorem merge.ConflictsFromManagers.wp_proof
    (h_Path_Copy : fieldpath.Path.Copy.spec (GF := GF))
    (h_Set_Iterate : fieldpath.Set.Iterate.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF)) :
    merge.ConflictsFromManagers.spec (GF := GF) :=
    fun sets cmf => by
  wp_start as #Hmf
  ihave ⟨%M, #HM, %hM, #HE⟩ := isMF_read sets cmf $$ Hmf
  obtain ⟨hMs, hMk⟩ := hM
  wp_auto
  wp_apply (wp_slice_literal (V := merge.Conflict) [])
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, Hcap0⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (j : Int) => iprop(∃ (sl : GoSlice)
      (xs : List merge.Conflict) (l : List (GoString × Path)) (y : GoInterface),
      "%Hj" ∷ ⌜0 ≤ j⌝ ∗
      "%Hl" ∷ ⌜l.Nodup ∧ ∀ c, c ∈ l ↔ pairVis cmf (keys.take j.toNat) c⌝ ∗
      "Hsl" ∷ sl ↦* xs ∗
      "Hcap" ∷ ownSliceCap merge.Conflict sl (DFrac.own 1) ∗
      "HL" ∷ isConflictL xs l ∗
      "conflicts" ∷ conflicts_ptr ↦ sl ∗
      "set" ∷ set_ptr ↦ y)) $$ HM
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hsl0 Hcap0 conflicts set]
  · iexists _, [], [], _
    simp only [named]
    iframe
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro
      refine ⟨List.nodup_nil, fun c => ?_⟩
      simp [pairVis]
    simp only [isConflictL]; itrivial
  isplitr
  · imodintro
    iintro %j %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    obtain ⟨e, he⟩ : ∃ e, cmf.get key = some e :=
      Option.isSome_iff_exists.1 (by rw [← hMk, Hv]; rfl)
    ihave #Hve := HE $$ %key %v %e %(⟨Hv, he⟩)
    ihave ⟨%vv, %hvv⟩ := isVSet_concrete_law_holds v e $$ Hve
    subst hvv
    wp_auto
    wp_func_lits
    wp_apply (h_versionedSet_Set vv e) as %sp #Hsp
    · iexact Hve
    wp_apply (h_Set_Iterate sp e.set _ (fun done => iprop(∃ (sl' : GoSlice) (xs' : List merge.Conflict),
        "Hsl" ∷ sl' ↦* xs' ∗
        "Hcap" ∷ ownSliceCap merge.Conflict sl' (DFrac.own 1) ∗
        "HL" ∷ isConflictL xs' (l ++ done.map (fun q => (key, q))) ∗
        "conflicts" ∷ conflicts_ptr ↦ sl' ∗
        "manager" ∷ manager_ptr ↦ key))) $$ [Hsl Hcap HL conflicts manager]
        as ⟨%done, ⟨%hdnd, %hdset⟩, HI⟩
    · iframe Hsp
      isplitl [Hsl Hcap HL conflicts manager]
      · iexists sl, xs
        simp only [named, List.map_nil, List.append_nil]
        iframe
      imodintro
      iintro %done %q %s %dq ⟨%hq, %hqd⟩
      imodintro
      iintro %Φ' ⟨HI, Hq⟩ HΦ'
      iNamed HI
      wp_auto
      wp_method_call
      try wp_auto
      wp_apply (h_Path_Copy s dq q) $$ [Hq] as %s' ⟨Hq, Hs'⟩
      · iexact Hq
      imod (isPathF_persist_law_holds _ _ _) $$ Hs' with #Hs'
      try wp_auto
      wp_apply (wp_slice_literal (V := merge.Conflict) [{ Manager' := key, Path' := s' }])
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hosl] as %sl2 ⟨Hsl, Hcap, -⟩
      try wp_auto
      iapply HΦ'
      iframe Hq
      iexists sl2, _
      simp only [named]
      iframe
      rw [List.map_append, ← List.append_assoc, List.map_singleton]
      iapply (isConflictL_snoc xs' _ { Manager' := key, Path' := s' } key q) $$ [HL] %rfl
      iframe HL Hs'
    iNamed HI
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _, _, _, _
    simp only [named]
    iframe
    isplitr
    · ipureintro; omega
    ipureintro
    exact pairVis_step cmf keys j key e l done Hj Hkey Hknodup he Hl ⟨hdnd, hdset⟩
  iintro HP -
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hl
  imod (ownSlice_persist _ _ _) $$ Hsl with #Hsl
  wp_auto
  iapply HΦ
  iexists l
  isplitr
  · ipureintro
    refine ⟨Hl.1, FSet.ext' (fun c => ?_)⟩
    rw [FSet.mem_ofList', Hl.2, pairVis_all cmf keys hMs (fun k => by rw [Hkset k, hMk k])]
  unfold isConflicts
  iexists xs
  iframe Hsl HL

end proof

end smd
end EtcdGrove
end Perennial
