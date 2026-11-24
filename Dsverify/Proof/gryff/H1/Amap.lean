/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Amap.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: `amapRep` (a Go map of objects mirroring a model `AMap`): taking an entry out, putting
one back, deleting one.
-/
module

public import Dsverify.Proof.gryff.H1.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (AMap)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

/-- The entries of an `amapRep`. -/
def amapEnts {n : Nat} {V : Type} (am : AMap n V) (m : GMap (BitVec n) Loc)
    (R : Loc → V → IProp GF) : IProp GF :=
  iprop([∗map] key ↦ p ∈ m, ∃ v, ⌜am.get? key = some v⌝ ∗ R p v)

theorem amapRep_open {n : Nat} {V : Type} (mR : Loc) (am : AMap n V)
    (R : Loc → V → IProp GF) :
    amapRep mR am R ⊣⊢ ∃ m : GMap (BitVec n) Loc, mR ↦$ m ∗
      ⌜∀ key, (m.lookup key).isSome = (am.get? key).isSome⌝ ∗ amapEnts am m R := .rfl

theorem amapEnts_congr {n : Nat} {V : Type} (am am' : AMap n V) (m : GMap (BitVec n) Loc)
    (R : Loc → V → IProp GF) (h : ∀ k, am.get? k = am'.get? k) :
    amapEnts am m R ⊢ amapEnts am' m R := by
  unfold amapEnts
  refine BigSepM.bigSepM_mono (fun {k v} _ => ?_)
  iintro ⟨%x, %Hx, H⟩
  iexists x
  iframe H
  ipureintro; rw [← h]; exact Hx

theorem amapEnts_take {n : Nat} {V : Type} (am : AMap n V) (m : GMap (BitVec n) Loc)
    (R : Loc → V → IProp GF) (key : BitVec n) (p : Loc) (hp : m !! key = some p) :
    amapEnts am m R ⊢ amapEnts am (GMap.delete key m) R ∗
      ∃ v, ⌜am.get? key = some v⌝ ∗ R p v := by
  unfold amapEnts
  refine (BigSepM.bigSepM_delete (M := GMap (BitVec n)) (i := key) (x := p) hp).1.trans ?_
  iintro ⟨H, Hrest⟩
  iframe Hrest H

theorem amapEnts_put {n : Nat} {V : Type} (am : AMap n V) (m : GMap (BitVec n) Loc)
    (R : Loc → V → IProp GF) (key : BitVec n) (p : Loc) (v : V) :
    amapEnts am (GMap.delete key m) R ∗ R p v ⊢ amapEnts (am.put key v) (<[key := p]> m) R := by
  unfold amapEnts
  have Hm : ([∗map] k ↦ q ∈ GMap.delete key m, ∃ x, ⌜am.get? k = some x⌝ ∗ R q x) ⊢
      ([∗map] k ↦ q ∈ GMap.delete key m, ∃ x, ⌜(am.put key v).get? k = some x⌝ ∗ R q x) :=
    BigSepM.bigSepM_mono (M := GMap (BitVec n)) (fun {k q} hk => by
      have hne : k ≠ key := by
        intro he; subst he
        change (GMap.delete k m) !! k = some q at hk; rw [GMap.lookup_delete] at hk; cases hk
      iintro ⟨%x, %Hx, H⟩
      iexists x
      iframe H
      ipureintro; rw [amap_put_get]; simp [hne, Hx])
  iintro ⟨Hrest, H⟩
  iapply (BigSepM.bigSepM_insert_delete (M := GMap (BitVec n)) (m := m) (i := key) (x := p)
    (Φ := fun k q => iprop(∃ x, ⌜(am.put key v).get? k = some x⌝ ∗ R q x))).2
  isplitl [H]
  · iexists v
    iframe H
    ipureintro; rw [amap_put_get]; simp
  iapply Hm $$ Hrest

theorem amapEnts_update {n : Nat} {V : Type} (am : AMap n V) (m : GMap (BitVec n) Loc)
    (R : Loc → V → IProp GF) (key : BitVec n) (p : Loc) (v : V) (hp : m !! key = some p) :
    amapEnts am (GMap.delete key m) R ∗ R p v ⊢ amapEnts (am.put key v) m R := by
  have h := amapEnts_put am m R key p v
  rw [GMap.insert_id _ _ _ hp] at h
  exact h

theorem amapEnts_del {n : Nat} {V : Type} (am : AMap n V) (m : GMap (BitVec n) Loc)
    (R : Loc → V → IProp GF) (key : BitVec n) :
    amapEnts am (GMap.delete key m) R ⊢ amapEnts (am.del key) (GMap.delete key m) R := by
  unfold amapEnts
  refine BigSepM.bigSepM_mono (M := GMap (BitVec n)) (fun {k q} hk => ?_)
  have hne : k ≠ key := by
    intro he; subst he
    change (GMap.delete k m) !! k = some q at hk; rw [GMap.lookup_delete] at hk; cases hk
  iintro ⟨%x, %Hx, H⟩
  iexists x
  iframe H
  ipureintro; rw [amap_del_get_ne _ _ _ hne]; exact Hx

/-- Drop an entry (its object is leaked). -/
theorem amapEnts_drop {n : Nat} {V : Type} (am : AMap n V) (m : GMap (BitVec n) Loc)
    (R : Loc → V → IProp GF) (key : BitVec n) :
    amapEnts am m R ⊢ amapEnts (am.del key) (GMap.delete key m) R := by
  cases hk : m !! key with
  | none =>
    have := amapEnts_del am m R key
    rw [GMap.delete_notin _ _ hk] at this ⊢
    exact this
  | some p =>
    refine (amapEnts_take am m R key p hk).trans ?_
    refine BI.sep_elim_left.trans ?_
    exact amapEnts_del am m R key

end

end Perennial.gryff.replica2
