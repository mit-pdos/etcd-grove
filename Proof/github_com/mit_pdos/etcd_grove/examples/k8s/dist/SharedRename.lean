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
  obtain ⟨l, d⟩ := st
  unfold setStepI
  simp only [renItem_key]
  by_cases h2 : e.key' = it.key' <;> cases d <;> by_cases h1 : go.GoStringLt it.key' e.key' <;>
    simp [h1, h2, go.goStringLt_irrefl]

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
  dsimp only
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
      rw [h]; congr 1; word
  simp only [preOkL, renObj]
  by_cases hp : x.HasPreRV' = true
  · simp only [hp, if_true]
    congr 1
    exact decide_eq_decide.mpr key
  · simp only [hp]; rfl

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

/-! ## The cut property -/

/-- **`ρ` cuts `w` like the identity**: every anchor `v`, and the revision after it, is at most `w`
exactly when it is at most `ρ w` (`canonL_cut`). -/
def CutW (A : List Nat) (ρ : Nat → Nat) (w : Nat) : Prop :=
  ∀ v ∈ A, (v ≤ w ↔ v ≤ ρ w) ∧ (v + 1 ≤ w ↔ v + 1 ≤ ρ w)

/-- A revision whose image is an anchor is not renamed. -/
theorem CutW.fix {A : List Nat} {ρ : Nat → Nat} {w : Nat} (h : CutW A ρ w) (ha : ρ w ∈ A) :
    ρ w = w := by
  obtain ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := h _ ha
  have := h1' (Nat.le_refl _)
  rcases Nat.lt_or_ge (ρ w) w with hl | hl
  · have := h2 hl; omega
  · omega

/-- The image of `w` is the anchor `r` exactly when `w` is. -/
theorem CutW.eq_iff {A : List Nat} {ρ : Nat → Nat} {w r : Nat} (h : CutW A ρ w) (hr : r ∈ A) :
    ρ w = r ↔ w = r := by
  obtain ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := h _ hr
  constructor
  · intro e
    have := h1' (by omega)
    rcases Nat.lt_or_ge r w with hl | hl
    · have := h2 hl; omega
    · omega
  · intro e
    have := h1 (by omega)
    rcases Nat.lt_or_ge r (ρ w) with hl | hl
    · have := h2' hl; omega
    · omega

/-! ## A write's step on renamed stores -/

/-- An object at the revision `a`, renamed by a `ρ` taking `a` to `b`, is at `b`. -/
theorem renObj_setRV (ρ : Nat → Nat) (o : Obj) (a b : w64) (h : ρ (uint.nat a) = uint.nat b) :
    renObj ρ { o with ResourceVersion' := a } = { o with ResourceVersion' := b } := by
  simp only [renObj, h]
  rw [show (W64 (uint.nat b : Int)) = b by word]

theorem renObj_zObj (ρ : Nat → Nat) (hz : ρ 0 = 0) : renObj ρ zObj = zObj := by
  simp [renObj, zObj, hz]

theorem lookupL_mem (its : List item) (k : GoString) (h : (lookupL its k).2 = true) :
    (lookupL its k).1 ∈ its := by
  unfold lookupL at h ⊢
  cases hf : its.find? (fun it => decide (it.key' = k)) with
  | none => rw [hf] at h; simp at h
  | some it => exact List.mem_of_find?_eq_some hf

/-- **How a write's step on two related stores relates the results**: the items stay renamed, and
both stores take a revision or neither does. -/
def StepRen (ρ : Nat → Nat) (s c s' c' : GSt) : Prop :=
  c'.items = s'.items.map (renItem ρ) ∧
    ((s'.rv = s.rv ∧ c'.rv = c.rv) ∨ (s'.rv = s.rv + W64 1 ∧ c'.rv = c.rv + W64 1))

/-- What the write step needs of the renaming: it fixes 0, it takes the search's next revision to
the cluster's, it keeps every stored revision below `2^64`, and it keeps each stored object's
revision equal to a resource-version precondition's exactly when it is. -/
structure WriteRen (ρ : Nat → Nat) (x : Input) (its : List item) (a b : w64) : Prop where
  zero : ρ 0 = 0
  next : ρ (uint.nat a + 1) = uint.nat b + 1
  a_lt : uint.nat a + 1 < 2 ^ 64
  b_lt : uint.nat b + 1 < 2 ^ 64
  fits : ∀ it ∈ its, ρ (uint.nat it.obj'.ResourceVersion') < 2 ^ 64
  pre : ∀ r, parseRVD x.PreRV' = some r → ∀ it ∈ its,
    (ρ (uint.nat it.obj'.ResourceVersion') = uint.nat r ↔ uint.nat it.obj'.ResourceVersion' = uint.nat r)

theorem WriteRen.next_w {ρ : Nat → Nat} {x : Input} {its : List item} {a b : w64}
    (h : WriteRen ρ x its a b) : ρ (uint.nat (a + W64 1)) = uint.nat (b + W64 1) := by
  have h1 : uint.nat (a + W64 1) = uint.nat a + 1 := by have := h.a_lt; word
  have h2 : uint.nat (b + W64 1) = uint.nat b + 1 := by have := h.b_lt; word
  rw [h1, h2]; exact h.next

/-- The looked-up object's preconditions are the same renamed. -/
theorem WriteRen.preOk {ρ : Nat → Nat} {x : Input} {its : List item} {a b : w64}
    (h : WriteRen ρ x its a b) (k : GoString) (hk : (lookupL its k).2 = true) :
    preOkL x (renObj ρ (lookupL its k).1.obj') = preOkL x (lookupL its k).1.obj' :=
  preOkL_ren ρ x _ (h.fits _ (lookupL_mem its k hk))
    (fun r hr => h.pre r hr _ (lookupL_mem its k hk))

theorem mcreateL_ren (ρ : Nat → Nat) (x : Input) (its : List item) (a b : w64)
    (h : WriteRen ρ x its a b) :
    StepRen ρ ⟨its, a⟩ ⟨its.map (renItem ρ), b⟩ (mcreateL x ⟨its, a⟩).1
      (mcreateL x ⟨its.map (renItem ρ), b⟩).1 := by
  unfold mcreateL
  simp only [lookupL_ren ρ h.zero]
  split
  · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · refine ⟨?_, Or.inr ⟨rfl, rfl⟩⟩
    simp only
    rw [← setItemL_ren]
    congr 1
    simp only [renItem]
    congr 1
    exact (renObj_setRV ρ ⟨(splitKeyL x.Key').1, (splitKeyL x.Key').2, x.UID', x.Val', x.Node',
      x.App', a + W64 1, false⟩ _ _ h.next_w).symm

theorem renObj_node (ρ : Nat → Nat) (o : Obj) : (renObj ρ o).Node' = o.Node' := rfl

theorem mdeleteL_ren (ρ : Nat → Nat) (x : Input) (its : List item) (a b : w64)
    (h : WriteRen ρ x its a b) :
    StepRen ρ ⟨its, a⟩ ⟨its.map (renItem ρ), b⟩ (mdeleteL x ⟨its, a⟩).1
      (mdeleteL x ⟨its.map (renItem ρ), b⟩).1 := by
  unfold mdeleteL
  simp only [lookupL_ren ρ h.zero]
  by_cases hk : (lookupL its x.Key').2 = true
  · simp only [hk, Bool.not_true, Bool.false_eq_true, if_false, renItem_obj, h.preOk x.Key' hk,
      renObj_node]
    rcases Bool.eq_false_or_eq_true (preOkL x (lookupL its x.Key').1.obj') with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (rejects x.HasReject' x.Reject' (lookupL its x.Key').1.obj'.Node')
      with hr | hr <;>
    simp only [hp, hr, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true, if_false] <;>
    first
      | exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
      | exact ⟨delItemL_ren ρ its x.Key', Or.inr ⟨rfl, rfl⟩⟩
  · simp only [Bool.not_eq_true] at hk
    simp only [hk, Bool.not_false, if_true]
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem mupdateL_ren (ρ : Nat → Nat) (x : Input) (its : List item) (a b : w64)
    (h : WriteRen ρ x its a b) :
    StepRen ρ ⟨its, a⟩ ⟨its.map (renItem ρ), b⟩ (mupdateL x ⟨its, a⟩).1
      (mupdateL x ⟨its.map (renItem ρ), b⟩).1 := by
  unfold mupdateL
  simp only [lookupL_ren ρ h.zero, renItem_obj, renItem_canon]
  -- the current object, renamed
  have hcur : (if (lookupL its x.Key').2 = true then renObj ρ (lookupL its x.Key').1.obj' else zObj) =
      renObj ρ (if (lookupL its x.Key').2 = true then (lookupL its x.Key').1.obj' else zObj) := by
    split
    · rfl
    · exact (renObj_zObj ρ h.zero).symm
  have hpre : preOkL x (renObj ρ (if (lookupL its x.Key').2 = true then (lookupL its x.Key').1.obj'
      else zObj)) = preOkL x (if (lookupL its x.Key').2 = true then (lookupL its x.Key').1.obj'
      else zObj) := by
    by_cases hk : (lookupL its x.Key').2 = true
    · simp only [hk, if_true]; exact h.preOk x.Key' hk
    · simp only [hk, if_false, Bool.false_eq_true]; rw [renObj_zObj ρ h.zero]
  rw [hcur, hpre, updatedL_ren, sameObjL_ren, renObj_node]
  generalize (if (lookupL its x.Key').2 = true then (lookupL its x.Key').1.obj' else zObj) = cur
  rcases Bool.eq_false_or_eq_true (!(lookupL its x.Key').2 && !x.IgnoreNotFound') with hn | hn <;>
  simp only [hn, Bool.false_eq_true, if_true, if_false]
  · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rcases Bool.eq_false_or_eq_true (preOkL x cur) with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (rejects x.HasReject' x.Reject' cur.Node') with hr | hr <;>
    simp only [hp, hr, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true, if_false]
    all_goals try exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    by_cases hs : ((lookupL its x.Key').2 = true ∧ sameObjL (updatedL x cur) (lookupL its x.Key').1.obj' = true ∧
      (lookupL its x.Key').1.canon' = true)
    · simp only [hs, if_true]; exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · simp only [hs, if_false]
      refine ⟨?_, Or.inr ⟨rfl, rfl⟩⟩
      rw [← setItemL_ren]
      congr 1
      simp only [renItem]
      congr 1
      rw [renObj_setRV ρ _ _ _ h.next_w]
      simp only [renObj]

/-- **A write's (or a read's) step on renamed stores**: the items stay renamed, and both stores take a
revision or neither does. -/
theorem mstepL_ren (ρ : Nat → Nat) (x : Input) (its : List item) (a b : w64)
    (h : WriteRen ρ x its a b) :
    StepRen ρ ⟨its, a⟩ ⟨its.map (renItem ρ), b⟩ (mstepL x ⟨its, a⟩).1
      (mstepL x ⟨its.map (renItem ρ), b⟩).1 := by
  unfold mstepL
  split
  · exact mcreateL_ren ρ x its a b h
  · split
    · exact mdeleteL_ren ρ x its a b h
    · split
      · exact mupdateL_ren ρ x its a b h
      · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- **An object an answer shows is not renamed**: its renamed revision is an anchor, so the renaming
fixes it (`CutW.fix`). -/
theorem renObj_fix {A : List Nat} {ρ : Nat → Nat} (o : Obj)
    (hc : CutW A ρ (uint.nat o.ResourceVersion')) (hf : ρ (uint.nat o.ResourceVersion') < 2 ^ 64)
    (hA : uint.nat (renObj ρ o).ResourceVersion' ∈ A) : renObj ρ o = o := by
  have hn : uint.nat (renObj ρ o).ResourceVersion' = ρ (uint.nat o.ResourceVersion') := by
    simp only [renObj]; word
  rw [hn] at hA
  have he := hc.fix hA
  simp only [renObj, he]
  rw [show (W64 (uint.nat o.ResourceVersion' : Int)) = o.ResourceVersion' by word]

end go

end k8s_dist
end EtcdGrove
end Perennial
