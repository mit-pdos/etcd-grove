/-
Shared by the proofs of the index's reads (`Get`, `Revisions`, `CountRevisions`, `Range`):
the shape of `keyIndex.get`'s answer, that the tree's key indexes are never empty, and the
Boolean conditions of the range visitors. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `kiGetVal` is a 4-tuple of typed values (two revisions, a version and an error): the
components are `#x`, so the pure steps of a function returning them (each a `let` of a value
that is not a panic) go through. -/
theorem kiGetVal_pairs (ki : mvcc.KeyIndex) (atRev : w64) (e : GoInterface) :
    ∃ (m c : Revision) (v : w64) (i : GoInterface),
      mvcc.kiGetVal ki atRev e = PairV (PairV (PairV #m #c) #v) #i := by
  unfold mvcc.kiGetVal
  cases mvcc.kiGet ki atRev with
  | none => exact ⟨_, _, _, _, rfl⟩
  | some r => obtain ⟨m, c, v⟩ := r; exact ⟨_, _, _, _, rfl⟩

/-- Every key index of the tree (the index of some events) has a revision. -/
theorem entries_not_empty (L : List mvcc.IdxEntry) (evs : List mvcc.Ev)
    (h : mvcc.idxOfEntries L = mvcc.indexOf evs) : ∀ z ∈ L, mvcc.kiIsEmpty z.2.2 = false := by
  intro z hz
  have : (z.2.1, z.2.2) ∈ mvcc.indexOf evs := by
    rw [← h]; unfold mvcc.idxOfEntries; exact List.mem_map_of_mem hz
  exact (mvcc.kiIsEmpty_false_of_head (mvcc.indexOf_head' evs _ this)).1

/-- Every key index of the tree (compacted, `IdxCRep`) has a revision. -/
theorem entries_not_emptyC (L : List mvcc.IdxEntry) (evs : List mvcc.Ev) (cmax : Int)
    (h : mvcc.IdxCRep cmax evs (mvcc.idxOfEntries L)) : ∀ z ∈ L, mvcc.kiIsEmpty z.2.2 = false := by
  intro z hz
  have hmem : (z.2.1, z.2.2) ∈ mvcc.idxOfEntries L := by
    unfold mvcc.idxOfEntries; exact List.mem_map_of_mem hz
  have hg := mvcc.idxGet_of_mem _ h.1 _ hmem
  obtain ⟨c, -, -, -, hne⟩ := mvcc.IdxCRep.get_some h hg
  exact hne

/-- `limit > 0 && len(revs) >= limit`, as Goose compiles it (the first conjunct already a value):
`reached`. -/
theorem wp_reachedLimit {V : Type} (t : go.GoType) [ZeroVal V] [TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V t] (limit : w64) (limit_ptr sl_ptr : Loc) (rs : GoSlice) (vs : List V) :
    {{ (limit_ptr ↦□ limit : IProp GF) ∗ sl_ptr ↦ rs ∗ rs ↦* vs }}
      (If (Val #(decide (sint.Z (W64 0) < sint.Z limit)))
        (App (Val (GoInstruction (GoOp GoGe go.int)))
          (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType t)))) (Val #sl_ptr))
                  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType t)])))
                    (Val #())) (Var "$a0")))
                (App (Val (GoInstruction (GoLoad go.int))) (Val #limit_ptr))))
        (Val #false))
    {{ (b : Bool), RET #b; ⌜b = mvcc.reached (mvcc.limitOf limit) vs.length⌝ ∗ sl_ptr ↦ rs ∗ rs ↦* vs }} := by
  wp_start as ⟨#Hl, Hrs, Hsl⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iframe Hrs Hsl
    ipureintro
    unfold mvcc.limitOf mvcc.reached
    have h0 : (0 : Int) < sint.Z limit := by
      have h := Hif; rw [show sint.Z (W64 0) = 0 by decide] at h; exact h
    simp only [h0, ↓reduceIte]
    obtain ⟨h1, h2⟩ := Hlen
    rw [h1]
    unfold sint.nat sint.Z at *
    simp only [decide_eq_decide]
    omega
  · (try wp_auto)
    iapply HΦ
    iframe Hrs Hsl
    ipureintro
    unfold mvcc.limitOf mvcc.reached
    have h0 : ¬ (0 : Int) < sint.Z limit := by
      have h := Hif; rw [show sint.Z (W64 0) = 0 by decide] at h; exact h
    simp [h0]

/-- `reachedLimit && !withTotalCount` (`reachedLimit` already loaded). -/
theorem wp_stopCond (b wt : Bool) (wt_ptr : Loc) :
    {{ (wt_ptr ↦□ wt : IProp GF) }}
      (If (Val #b)
        (App (Val (GoInstruction (GoUnOp GoNot go.bool)))
          (App (Val (GoInstruction (GoLoad go.bool))) (Val #wt_ptr)))
        (Val #false))
    {{ RET #(b && !wt); True }} := by
  wp_start as #Hwt
  cases b
  · (try wp_auto)
    simp only [Bool.false_and]
    iapply HΦ
    itrivial
  · wp_auto
    simp only [Bool.true_and]
    iapply HΦ
    itrivial

end lemmas

end EtcdGrove
end Perennial
