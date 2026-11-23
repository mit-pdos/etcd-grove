/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/queue/Base.lean`, run `rabia-r1wake-1`.)

Shared definitions and lemmas of `rabia/internal/queue`'s proofs: the representation of a
`PQueue`'s elements (`reps`, the last conjunct of `pqOwn`) and its transport along the
permutations the methods do.
-/
module

public import Dsverify.Proof.rabia.internal.queue.Spec
public import Perennial.Proof.sort.SorterBasics

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.queue

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

/-- The order of `PQueue.Less` (`ProxySeqIdLessThan`) on the objects' records. -/
def objLt (a b : ObjV) : Prop :=
  a.proSeq.toNat < b.proSeq.toNat ∨ (a.proSeq = b.proSeq ∧ a.proId.toNat < b.proId.toNat)

/-- A swap of two positions, done in both lists: each new position holds an old one's pair. -/
theorem swap_transport {α β : Type} (vs : List α) (xs : List β) (i j : Nat) (vi vj : α) (a b : β)
    (hvi : vs[i]? = some vi) (hvj : vs[j]? = some vj) (ha : xs[i]? = some a)
    (hb : xs[j]? = some b) :
    ∀ (k : Nat) (v' : α), ((vs.set i vj).set j vi)[k]? = some v' →
      ∃ k0 : Nat, vs[k0]? = some v' ∧ ((xs.set i b).set j a)[k]? = xs[k0]? := by
  have hil := (List.getElem?_eq_some_iff.mp hvi).1
  have hjl := (List.getElem?_eq_some_iff.mp hvj).1
  have hil' := (List.getElem?_eq_some_iff.mp ha).1
  have hjl' := (List.getElem?_eq_some_iff.mp hb).1
  intro k v' hk
  by_cases hkj : k = j
  · subst hkj
    refine ⟨i, ?_, ?_⟩
    · simp [hjl] at hk; rw [hvi, hk]
    · simp [hjl', ha]
  by_cases hki : k = i
  · subst hki
    refine ⟨j, ?_, ?_⟩
    · simp [Ne.symm hkj, hil] at hk; rw [hvj, hk]
    · simp [Ne.symm hkj, hil', hb]
  · refine ⟨k, ?_, ?_⟩
    · simpa [Ne.symm hkj, Ne.symm hki] using hk
    · simp [Ne.symm hkj, Ne.symm hki]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The Go values `vs` hold the records `xs` (index by index). -/
def reps (vs : List ConsensusObj) (xs : List ObjV) : IProp GF :=
  iprop([∗list] i ↦ v ∈ vs, ∃ o, ⌜xs[i]? = some o⌝ ∗ objRep v o)

instance reps_persistent (vs : List ConsensusObj) (xs : List ObjV) :
    Persistent (reps (GF := GF) vs xs) := by
  unfold reps; infer_instance

/-- The `heap.Interface` value of `&q`, as a `GoInterfaceOk`. -/
def pqx (q : Loc) : GoInterfaceOk := ⟨go.GoType.PointerType PQueue.ty, #q⟩

omit [GooseSemantics] [GooseInterp] in
theorem pqIface_eq (q : Loc) : pqIface q = interface.ok (pqx q) := rfl

theorem pqOwn_unfold (q : Loc) (xs : List ObjV) :
    pqOwn (GF := GF) q xs = iprop(∃ (sl : GoSlice) (vs : List ConsensusObj), q ↦ sl ∗ sl ↦* vs ∗
      ownSliceCap ConsensusObj sl (DFrac.own 1) ∗ ⌜vs.length = xs.length⌝ ∗ reps vs xs) := rfl

/-- `reps` along a re-indexing: every new position holds an old position's pair. -/
theorem reps_transport (vs vs' : List ConsensusObj) (xs xs' : List ObjV)
    (h : ∀ (k : Nat) (v' : ConsensusObj), vs'[k]? = some v' → ∃ k0 : Nat, vs[k0]? = some v' ∧ xs'[k]? = xs[k0]?) :
    reps (GF := GF) vs xs ⊢ reps vs' xs' := by
  unfold reps
  iintro #H
  ihave #H := BigSepL.bigSepL_forall_intro $$ H
  iapply BigSepL.bigSepL_forall_elim
  iintro %k %v' %hk
  obtain ⟨k0, h0, hx⟩ := h k v' hk
  ispecialize H $$ %k0 %v'
  icases H $$ %h0 with ⟨%o, %ho, #Hr⟩
  iexists o
  iframe Hr
  ipureintro; rw [hx]; exact ho

theorem reps_lookup (vs : List ConsensusObj) (xs : List ObjV) (i : Nat) (v : ConsensusObj)
    (h : vs[i]? = some v) :
    reps (GF := GF) vs xs ⊢ ∃ o, ⌜xs[i]? = some o⌝ ∗ objRep v o := by
  unfold reps
  iintro #H
  iapply (BigSepL.bigSepL_lookup (Φ := fun i v => iprop(∃ o, ⌜xs[i]? = some o⌝ ∗ objRep (GF := GF) v o)) h)
  iexact H

theorem reps_snoc (vs : List ConsensusObj) (xs : List ObjV) (v : ConsensusObj) (o : ObjV)
    (hl : vs.length = xs.length) :
    (reps (GF := GF) vs xs ∗ objRep v o) ⊢ reps (vs ++ [v]) (xs ++ [o]) := by
  unfold reps
  iintro ⟨#H, #Ho⟩
  iapply BigSepL.bigSepL_snoc.2
  isplitl []
  · iapply BigSepL.bigSepL_mono ?_ $$ H
    intro k x hk
    iintro ⟨%o', %ho', #Hr⟩
    iexists o'
    iframe Hr
    ipureintro
    have hk' : k < xs.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1; omega
    rw [List.getElem?_append_left hk']; exact ho'
  · iexists o
    iframe Ho
    ipureintro
    rw [hl]; simp

end defs

end Perennial.rabia.internal.queue
