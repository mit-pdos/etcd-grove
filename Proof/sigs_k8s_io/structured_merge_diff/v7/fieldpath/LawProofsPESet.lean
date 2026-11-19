/-
**Helpers for `fieldpath`'s sorted sets and maps of path elements** (`PathElementSet`,
`PathElementMap`, `PathElementValueMap`): sorted lists of well-formed elements, their merges, and
the representation's reading.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace fpA

/-- All elements well-formed. -/
abbrev AllWf (xs : List PE) : Prop := ∀ x ∈ xs, x.wf = true

theorem cmp_self (x : PE) (hx : x.wf = true) : PE.compare x x = 0 :=
  (PE_compare_eq_zero_law_holds x x hx hx).2 rfl

theorem lt_irrefl (x : PE) (hx : x.wf = true) : ¬ PE.lt x x := by
  unfold PE.lt; rw [cmp_self x hx]; decide

theorem sorted_nodup (xs : List PE) (hw : AllWf xs) (hs : PE.Sorted xs) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    unfold PE.Sorted at hs
    rw [List.pairwise_cons] at hs
    refine List.nodup_cons.2 ⟨fun hm => lt_irrefl x (hw x (by simp)) (hs.1 x hm), ?_⟩
    exact ih (fun y hy => hw y (by simp [hy])) hs.2

theorem hasCard_of_sorted (xs : List PE) (hw : AllWf xs) (hs : PE.Sorted xs) :
    (FSet.ofList xs).HasCard xs.length :=
  ⟨xs, sorted_nodup xs hw hs, rfl, rfl⟩

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fieldpath.Assumptions]

/-- A `PathElementSet`'s one field, and the way back. -/
theorem peset_members_acc (l : Loc) (v : fieldpath.PathElementSet) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢ l.[fieldpath.PathElementSet, go!"members"] ↦{dq} v.members' ∗
      (l.[fieldpath.PathElementSet, go!"members"] ↦{dq} v.members' -∗ l ↦{dq} v) := by
  iintro Hl
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %hn⟩
  iStructNamed Hl
  iframe members
  iintro Hm
  iapply typedPointsto_combine _ _ _ hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hm

end rep

end fpA

end smd
end EtcdGrove
end Perennial
