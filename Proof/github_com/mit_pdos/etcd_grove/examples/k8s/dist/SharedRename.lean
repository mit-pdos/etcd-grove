/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: renaming the stores' revisions

`notes/k8s-dist-k4.md` §3. The full mode's search lands each pending write at the canonical revision
`canonL` (`SharedPlace.lean`), at or below the cluster's; its stores are the cluster's with every
object's resource version renamed. Here: the renaming of an object, an item and a store's items
(`renObj ρ`, `renItem ρ`), and the store's helpers' invariance under it (`lookupL`, `delItemL`,
`setItemL`, the selectors, `sameObjL`, the preconditions), the first layer of `mstepL`'s invariance.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedSearch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section go
variable [GooseExts]

/-- An object with its resource version renamed by `ρ`. -/
def renObj (ρ : Nat → Nat) (o : Obj) : Obj :=
  { o with ResourceVersion' := W64 (ρ (uint.nat o.ResourceVersion') : Int) }

/-- An item with its object renamed by `ρ` (its key and `canon` flag unchanged). -/
def renItem (ρ : Nat → Nat) (it : item) : item := { it with obj' := renObj ρ it.obj' }

theorem renItem_key (ρ : Nat → Nat) (it : item) : (renItem ρ it).key' = it.key' := rfl

theorem renItem_canon (ρ : Nat → Nat) (it : item) : (renItem ρ it).canon' = it.canon' := rfl

theorem renItem_obj (ρ : Nat → Nat) (it : item) : (renItem ρ it).obj' = renObj ρ it.obj' := rfl

/-- A renaming fixing 0 leaves the zero item. -/
theorem renItem_zItem (ρ : Nat → Nat) (hz : ρ 0 = 0) : renItem ρ zItem = zItem := by
  simp [renItem, renObj, zItem, hz]

/-- **`lookupL` commutes with the renaming** (which fixes 0, the zero item's revision). -/
theorem lookupL_ren (ρ : Nat → Nat) (hz : ρ 0 = 0) (its : List item) (k : GoString) :
    lookupL (its.map (renItem ρ)) k = (renItem ρ (lookupL its k).1, (lookupL its k).2) := by
  unfold lookupL
  rw [List.find?_map]
  have : ((fun it : item => decide (it.key' = k)) ∘ renItem ρ) = fun it => decide (it.key' = k) := rfl
  rw [this]
  cases its.find? (fun it => decide (it.key' = k)) with
  | none => simp [renItem_zItem ρ hz]
  | some it => rfl

/-- **`delItemL` commutes with the renaming.** -/
theorem delItemL_ren (ρ : Nat → Nat) (its : List item) (k : GoString) :
    delItemL (its.map (renItem ρ)) k = (delItemL its k).map (renItem ρ) := by
  unfold delItemL
  rw [List.filter_map]
  rfl

/-- One step of `setItemL`'s loop commutes with the renaming. -/
theorem setStepI_ren (ρ : Nat → Nat) (it e : item) (st : List item × Bool) :
    setStepI (renItem ρ it) (st.1.map (renItem ρ), st.2) (renItem ρ e) =
      ((setStepI it st e).1.map (renItem ρ), (setStepI it st e).2) := by
  unfold setStepI
  simp only [renItem_key]
  by_cases h1 : st.2 = false ∧ go.GoStringLt it.key' e.key'
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : e.key' = it.key'
    · simp [h2]
    · simp [h2]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : e.key' = it.key'
    · by_cases h3 : st.2 = false
      · simp [h2, h3]
      · simp [h2, h3]
    · simp [h2]

theorem setItem_foldl_ren (ρ : Nat → Nat) (it : item) :
    ∀ (l : List item) (st : List item × Bool),
      (l.map (renItem ρ)).foldl (setStepI (renItem ρ it)) (st.1.map (renItem ρ), st.2) =
        ((l.foldl (setStepI it) st).1.map (renItem ρ), (l.foldl (setStepI it) st).2)
  | [], _ => rfl
  | e :: l, st => by
    simp only [List.map_cons, List.foldl_cons]
    rw [setStepI_ren]
    exact setItem_foldl_ren ρ it l _

/-- **`setItemL` commutes with the renaming.** -/
theorem setItemL_ren (ρ : Nat → Nat) (its : List item) (it : item) :
    setItemL (its.map (renItem ρ)) (renItem ρ it) = (setItemL its it).map (renItem ρ) := by
  unfold setItemL
  have := setItem_foldl_ren ρ it its ([], false)
  simp only [List.map_nil] at this
  rw [this]
  split <;> simp

/-- The selectors do not look at the resource version. -/
theorem selOkL_ren (ρ : Nat → Nat) (x : Input) (o : Obj) : selOkL x (renObj ρ o) = selOkL x o := rfl

/-- `sameObjL` does not look at the resource versions. -/
theorem sameObjL_ren (ρ ρ' : Nat → Nat) (a b : Obj) :
    sameObjL (renObj ρ a) (renObj ρ' b) = sameObjL a b := rfl

/-- `updatedL` keeps the renaming. -/
theorem updatedL_ren (ρ : Nat → Nat) (x : Input) (o : Obj) :
    updatedL x (renObj ρ o) = renObj ρ (updatedL x o) := by
  simp only [updatedL, updGo, renObj]; split <;> rfl

/-- **The preconditions are invariant** under a renaming that maps the object's revision to the
precondition's exactly when it is it (the precondition's revision is an anchor, which the renaming
fixes and no other revision maps to), below `2^64`. -/
theorem preOkL_ren (ρ : Nat → Nat) (x : Input) (o : Obj)
    (hb : ρ (uint.nat o.ResourceVersion') < 2 ^ 64)
    (hfix : ∀ r, parseRVD x.PreRV' = some r →
      (ρ (uint.nat o.ResourceVersion') = uint.nat r ↔ uint.nat o.ResourceVersion' = uint.nat r)) :
    preOkL x (renObj ρ o) = preOkL x o := by
  have key : x.PreRV' = rvStr (W64 (ρ (uint.nat o.ResourceVersion') : Int)) ↔
      x.PreRV' = rvStr o.ResourceVersion' := by
    have hn : uint.nat (W64 (ρ (uint.nat o.ResourceVersion') : Int)) = ρ (uint.nat o.ResourceVersion') := by
      word
    constructor
    · intro h
      have hp : parseRVD x.PreRV' = some (W64 (ρ (uint.nat o.ResourceVersion') : Int)) := by
        rw [h]; exact parseRVD_rvStr _
      have := (hfix _ hp).mp hn.symm
      have he : o.ResourceVersion' = W64 (ρ (uint.nat o.ResourceVersion') : Int) := by word
      rw [h, ← he]
    · intro h
      have hp : parseRVD x.PreRV' = some o.ResourceVersion' := by
        rw [h]; exact parseRVD_rvStr _
      have := (hfix _ hp).mpr rfl
      have he : o.ResourceVersion' = W64 (ρ (uint.nat o.ResourceVersion') : Int) := by word
      rw [h, he]
  simp only [preOkL, renObj]
  by_cases hp : x.HasPreRV' = true
  · simp only [hp, if_true]
    congr 1
    exact decide_eq_decide.mpr key
  · simp [hp]

/-- A preconditions' message is invariant under the same renaming, when it is the UID's or names an
anchor. -/
theorem preMsgL_ren_uid (ρ : Nat → Nat) (x : Input) (o : Obj)
    (h : (x.HasPreUID' && !decide (x.PreUID' = o.UID')) = true) :
    preMsgL x (renObj ρ o) = preMsgL x o := by
  have h' : (x.HasPreUID' && !decide (x.PreUID' = (renObj ρ o).UID')) = true := h
  simp only [preMsgL, h, h', if_true]; rfl

/-! ## Changes -/

/-- **No change between a store and itself.** -/
theorem changeAtL_self : ∀ (l : List item) (r : Nat), changeAtL l l r = none
  | [], _ => rfl
  | p :: ps, r => by
    simp only [changeAtL, go.goStringLt_irrefl, decide_false, Bool.false_eq_true, if_false,
      decide_true, if_true]
    exact changeAtL_self ps r

end go

end k8s_dist
end EtcdGrove
end Perennial
