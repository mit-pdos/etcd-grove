/-
Lean-first (no Rocq counterpart).

# The bridge to Kubernetes' checker, B1: one step (k8s 7g step 4)

`notes/k8s-7g-scope.md` §2.3, B1. On the abstraction of a driver's store (`absR`), the maintainers'
`Step` (`rstepL`) accepts the store's own answer to a write (`Raw`, as the checker's `Response`) and lands on
the abstraction of the driver's next store (`mstepL`), when the answer is what the output's plain fields
encode (`RawRel`; stage 7g option (C): a failed precondition's message is a plain field).

- `RawRel x y r`: the plain-field relation of the scope's premise "each output's `Raw` is the deep value its
  plain fields encode" (an object without the `Annotated` bit, a list with non-nil `Items`).
- `absR_items`, `absR_rewrites`, `absR_other`: the abstraction read through `lookupL`.
- `rstepL_write` (B1, writes): `Step` of a write's answer on `absR st` is accepted and moves to
  `absR (mstepL x st).1`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ModelFit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-! ## The plain-field relation -/

/-- **The store's answer `r` is what the output `y`'s plain fields encode** for the unary input `x`: an
object (its plain fields; the driver's objects are never `Annotated`), a list (its encoded items, never a nil
slice, its resource version, continue token and remaining count), or an error: "not found", "key exists" (key
and resource version), a callback's rejection (the delete's or the update's sentinel), "invalid object" (key
and `Check`'s message, stage 7g option (C)), too large. A client error (`EOther`) has no encoding. -/
def RawRel (x : Input) (y : Output) (r : RResp) : Prop :=
  if y.Err' = W64 0 then
    if x.Kind' = W64 4 then
      ∃ its, y.Items' = encItemsL its ∧ r = ⟨.list (some its) y.ListRV' y.Continue'
        (if y.HasRemaining' then some y.Remaining' else none), .none⟩
    else r = ⟨.obj (objOfL y), .none⟩
  else if y.Err' = W64 1 then r = ⟨.nil, .deep (.storageErr (W64 1) y.ErrKey' y.ErrRV' .nil)⟩
  else if y.Err' = W64 2 then r = ⟨.nil, .deep (.storageErr (W64 2) y.ErrKey' y.ErrRV' .nil)⟩
  else if y.Err' = W64 3 then r = ⟨.nil, if x.Kind' = W64 1 then delRejE else updRejE⟩
  else if y.Err' = W64 5 then
    r = ⟨.nil, .deep (.storageErr (W64 4) y.ErrKey' 0 (.errString y.ErrMsg'))⟩
  else if y.Err' = W64 6 then r = ⟨.nil, tooLargeE⟩
  else False

/-! ## The abstraction, read through `lookupL` -/

theorem lookupL_fI (its : List item) (n : GoString) :
    lookupL its n = ((fI its n).getD zItem, (fI its n).isSome) := by
  induction its with
  | nil => rfl
  | cons a t ih =>
    rw [lookupL_cons, fI_cons]
    by_cases h : a.key' = n <;> simp [h, ih]

theorem absR_items (st : GSt) (n : GoString) :
    (absR st).items !! storeKeyL n =
      if (lookupL st.items n).2 then some (lookupL st.items n).1.obj' else none := by
  show (GMap.ofList (st.items.map fun it => (storeKeyL it.key', it.obj'))) !! storeKeyL n = _
  rw [ofList_items, lookupL_fI]
  cases fI st.items n <;> rfl

theorem absR_rewrites (st : GSt) (hs : SortedI st.items) (n : GoString) :
    (absR st).rewrites !! storeKeyL n =
      if (lookupL st.items n).2 && !(lookupL st.items n).1.canon' then some true else none := by
  show (GMap.ofList ((st.items.filter fun it => !it.canon').map fun it => (storeKeyL it.key', true)))
    !! storeKeyL n = _
  rw [ofList_rewrites _ hs, lookupL_fI]
  cases e : fI st.items n with
  | none => rfl
  | some it => cases hc : it.canon' <;> simp [rwOf, hc]

theorem ofList_other {V : Type} (its : List item) (v : item → V) (k : GoString)
    (hk : ∀ n, k ≠ storeKeyL n) :
    (GMap.ofList (its.map fun it => (storeKeyL it.key', v it))) !! k = none := by
  induction its with
  | nil => rfl
  | cons a t ih =>
    show (<[storeKeyL a.key' := v a]> (GMap.ofList (t.map fun it => (storeKeyL it.key', v it)))) !! k = _
    rw [GMap.lookup_insert_ne _ _ (fun e => hk a.key' e.symm), ih]

theorem absR_other (st : GSt) (k : GoString) (hk : ∀ n, k ≠ storeKeyL n) :
    (absR st).items !! k = none ∧ (absR st).rewrites !! k = none := by
  refine ⟨ofList_other st.items (·.obj') k hk, ?_⟩
  show (GMap.ofList ((st.items.filter fun it => !it.canon').map fun it => (storeKeyL it.key', true)))
    !! k = none
  exact ofList_other _ (fun _ => true) k hk

/-- Two model states are equal when their fields and lookups agree. -/
theorem rm_ext {a b : RM} (hrv : a.rv = b.rv) (hp : a.pfx = b.pfx)
    (hi : ∀ k, a.items !! k = b.items !! k) (hr : ∀ k, a.rewrites !! k = b.rewrites !! k) :
    a = b := by
  cases a; cases b
  simp only at hrv hp
  subst hrv hp
  congr
  · exact GMap.ext hi
  · exact GMap.ext hr

/-- Every key is a store key or none (`∀ n, k ≠ storeKeyL n`). -/
theorem key_cases (k : GoString) : (∃ n, k = storeKeyL n) ∨ ∀ n, k ≠ storeKeyL n := by
  by_cases h : ∃ n, k = storeKeyL n
  · exact .inl h
  · exact .inr fun n e => h ⟨n, e⟩

/-- The model's precondition message, when the preconditions fail, is the driver's (`preMsg`). -/
theorem checkMsgL_preMsgL (x : Input) (o : Obj) (h : preOkL x o = false) :
    checkMsgL x o = some (preMsgL x o) := by
  unfold checkMsgL preMsgL
  unfold preOkL at h
  by_cases h1 : x.HasPreUID' = true <;> by_cases h2 : x.PreUID' = o.UID' <;>
    by_cases h3 : x.HasPreRV' = true <;> by_cases h4 : x.PreRV' = rvStr o.ResourceVersion' <;>
    simp_all

/-! ## B1: a write -/

/-- **The driver's store, as the model needs it**: sorted by key, and no stored object `Annotated` (the
driver's objects never are: `updGo` keeps the bit, `mcreate` clears it). -/
def StOk (st : GSt) : Prop := SortedI st.items ∧ ∀ it ∈ st.items, it.obj'.Annotated' = false

theorem lookupL_ann (st : GSt) (hst : StOk st) (n : GoString) (h : (lookupL st.items n).2 = true) :
    (lookupL st.items n).1.obj'.Annotated' = false := by
  rw [lookupL_fI] at h ⊢
  cases e : fI st.items n with
  | none => rw [e] at h; cases h
  | some it => exact hst.2 it (List.mem_of_find?_eq_some e)

theorem storeKeyL_ne {a b : GoString} (h : a ≠ b) : storeKeyL a ≠ storeKeyL b :=
  fun e => h (storeKeyL_inj e)

/-- A sorted store with a canonical item set: the abstraction's update (its rewrite flag cleared). -/
theorem absR_set (st : GSt) (hs : SortedI st.items) (it : item) (hc : it.canon' = true) (rv' : w64) :
    absR ⟨setItemL st.items it, rv'⟩ = { absR st with
      items := <[storeKeyL it.key' := it.obj']> (absR st).items, rv := rv',
      rewrites := GMap.delete (storeKeyL it.key') (absR st).rewrites } := by
  have hs' := sortedI_setItemL st.items it hs
  refine rm_ext rfl rfl ?_ ?_
  · intro k
    rcases key_cases k with ⟨n, rfl⟩ | hk
    · rw [show (absR ⟨setItemL st.items it, rv'⟩).items !! storeKeyL n = _ from
        absR_items ⟨setItemL st.items it, rv'⟩ n]
      simp only [lookupL_setItemL st.items it hs]
      by_cases h : it.key' = n
      · subst h; simp
      · simp only [h, if_false]
        rw [GMap.lookup_insert_ne _ _ (storeKeyL_ne h), absR_items]
    · rw [(absR_other _ k hk).1]
      show none = (<[storeKeyL it.key' := it.obj']> (absR st).items) !! k
      rw [GMap.lookup_insert_ne _ _ (fun e => hk it.key' e.symm), (absR_other _ k hk).1]
  · intro k
    rcases key_cases k with ⟨n, rfl⟩ | hk
    · rw [show (absR ⟨setItemL st.items it, rv'⟩).rewrites !! storeKeyL n = _ from
        absR_rewrites ⟨setItemL st.items it, rv'⟩ hs' n]
      simp only [lookupL_setItemL st.items it hs]
      by_cases h : it.key' = n
      · subst h; simp [hc]
      · simp only [h, if_false]
        show _ = (GMap.delete (storeKeyL it.key') (absR st).rewrites) !! storeKeyL n
        rw [GMap.lookup_delete_ne _ (storeKeyL_ne h), absR_rewrites _ hs]
    · rw [(absR_other _ k hk).2]
      show none = (GMap.delete (storeKeyL it.key') (absR st).rewrites) !! k
      rw [GMap.lookup_delete_ne _ (fun e => hk it.key' e.symm), (absR_other _ k hk).2]

/-- A key deleted: the abstraction's deletion. -/
theorem absR_del (st : GSt) (hs : SortedI st.items) (key : GoString) (rv' : w64) :
    absR ⟨delItemL st.items key, rv'⟩ = { absR st with
      items := GMap.delete (storeKeyL key) (absR st).items, rv := rv',
      rewrites := GMap.delete (storeKeyL key) (absR st).rewrites } := by
  have hs' := sortedI_delItemL st.items key hs
  refine rm_ext rfl rfl ?_ ?_
  · intro k
    rcases key_cases k with ⟨n, rfl⟩ | hk
    · rw [show (absR ⟨delItemL st.items key, rv'⟩).items !! storeKeyL n = _ from
        absR_items ⟨delItemL st.items key, rv'⟩ n]
      simp only [lookupL_delItemL]
      by_cases h : key = n
      · subst h; simp
      · simp only [h, if_false]
        show _ = (GMap.delete (storeKeyL key) (absR st).items) !! storeKeyL n
        rw [GMap.lookup_delete_ne _ (storeKeyL_ne h), absR_items]
    · rw [(absR_other _ k hk).1]
      show none = (GMap.delete (storeKeyL key) (absR st).items) !! k
      rw [GMap.lookup_delete_ne _ (fun e => hk key e.symm), (absR_other _ k hk).1]
  · intro k
    rcases key_cases k with ⟨n, rfl⟩ | hk
    · rw [show (absR ⟨delItemL st.items key, rv'⟩).rewrites !! storeKeyL n = _ from
        absR_rewrites ⟨delItemL st.items key, rv'⟩ hs' n]
      simp only [lookupL_delItemL]
      by_cases h : key = n
      · subst h; simp
      · simp only [h, if_false]
        show _ = (GMap.delete (storeKeyL key) (absR st).rewrites) !! storeKeyL n
        rw [GMap.lookup_delete_ne _ (storeKeyL_ne h), absR_rewrites _ hs]
    · rw [(absR_other _ k hk).2]
      show none = (GMap.delete (storeKeyL key) (absR st).rewrites) !! k
      rw [GMap.lookup_delete_ne _ (fun e => hk key e.symm), (absR_other _ k hk).2]

theorem respEqL_deep (o : DeepV) (d : DeepV) : respEqL ⟨o, .deep d⟩ ⟨o, .deep d⟩ = true := by
  simp [respEqL]

/-- B1 for a create. -/
theorem rcreateL_absR (x : Input) (st : GSt) (r : RResp) (hx : x.Kind' = W64 0)
    (hk : keyOkL (storeKeyL x.Key') = true) (hst : StOk st)
    (hrel : RawRel x (mcreateL x st).2 r) :
    (rcreateL x (absR st)).1 = r ∧ (rcreateL x (absR st)).2.1 = absR (mcreateL x st).1 := by
  have hx4 : x.Kind' ≠ W64 4 := by rw [hx]; decide
  unfold rcreateL
  unfold mcreateL at hrel ⊢
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hmem : storeKeyL x.Key' ∈ (absR st).items ↔ (lookupL st.items x.Key').2 = true := by
    rw [GMap.mem_iff, absR_items]; split <;> simp_all
  by_cases hf : (lookupL st.items x.Key').2 = true
  · rw [if_pos (hmem.2 hf)]
    simp only [hf, ↓reduceIte] at hrel ⊢
    simp [RawRel, existsL, errOutL] at hrel
    subst hrel
    exact ⟨rfl, rfl⟩
  · rw [if_neg (fun h => hf (hmem.1 h))]
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
    simp only [RawRel, objOutL, hx4, if_true, if_false] at hrel
    subst hrel
    refine ⟨rfl, ?_⟩
    rw [absR_set st hst.1 _ rfl]
    have hnone : (absR st).rewrites !! storeKeyL x.Key' = none := by
      rw [absR_rewrites _ hst.1]; simp [hf]
    refine rm_ext rfl rfl (fun _ => rfl) ?_
    intro k
    show (absR st).rewrites !! k = (GMap.delete (storeKeyL x.Key') (absR st).rewrites) !! k
    by_cases h : k = storeKeyL x.Key'
    · subst h; rw [hnone, GMap.lookup_delete]
    · rw [GMap.lookup_delete_ne _ (Ne.symm h)]

theorem objOfL_objOutL (o : Obj) (h : o.Annotated' = false) : objOfL (objOutL o) = o := by
  cases o; simp_all [objOfL, objOutL]

/-- B1 for a delete. -/
theorem rdeleteL_absR (x : Input) (st : GSt) (r : RResp) (hx : x.Kind' = W64 1)
    (hk : keyOkL (storeKeyL x.Key') = true) (hst : StOk st)
    (hrel : RawRel x (mdeleteL x st).2 r) :
    (rdeleteL x (absR st)).1 = r ∧ (rdeleteL x (absR st)).2.1 = absR (mdeleteL x st).1 := by
  have hx4 : x.Kind' ≠ W64 4 := by rw [hx]; decide
  unfold rdeleteL
  unfold mdeleteL at hrel ⊢
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, absR_items]
  by_cases hf : (lookupL st.items x.Key').2 = true
  · have ha := lookupL_ann st hst x.Key' hf
    simp only [hf, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at hrel ⊢
    cases hp : preOkL x (lookupL st.items x.Key').1.obj'
    · rw [checkMsgL_preMsgL _ _ hp]
      simp only [hp, Bool.not_false, ↓reduceIte] at hrel ⊢
      simp [RawRel, invalidObjL, invalidOutL] at hrel
      subst hrel; exact ⟨rfl, rfl⟩
    · rw [(checkMsgL_none _ _).2 hp]
      simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
      cases hrj : rejects x.HasReject' x.Reject' (lookupL st.items x.Key').1.obj'.Node'
      · simp only [hrj, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
        simp only [RawRel, objOutL, hx4, if_true, if_false] at hrel
        subst hrel
        refine ⟨?_, ?_⟩
        · simp only [ha]; rfl
        · rw [absR_del st hst.1]; rfl
      · simp only [hrj, ↓reduceIte] at hrel ⊢
        simp [RawRel, rejectedL, errOutL, hx] at hrel
        subst hrel; exact ⟨rfl, rfl⟩
  · simp only [hf, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hrel ⊢
    simp [RawRel, notFoundL, errOutL] at hrel
    subst hrel; exact ⟨rfl, rfl⟩

theorem noop_iff (a b : Obj) (h : a.Annotated' = b.Annotated') :
    decide ({ b with ResourceVersion' := 0 } = { a with ResourceVersion' := 0 }) = sameObjL a b := by
  cases a; cases b
  simp only at h
  subst h
  simp only [sameObjL]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro e
    simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk.injEq] at e
    obtain ⟨e1, e2, e3, e4, e5, e6, -, -⟩ := e
    exact ⟨⟨⟨⟨⟨e1.symm, e2.symm⟩, e3.symm⟩, e4.symm⟩, e5.symm⟩, e6.symm⟩
  · rintro ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩
    rw [e1, e2, e3, e4, e5, e6]

/-- B1 for an update. -/
theorem rupdateL_absR (x : Input) (st : GSt) (r : RResp) (hx : x.Kind' = W64 2)
    (hk : keyOkL (storeKeyL x.Key') = true) (hst : StOk st)
    (hrel : RawRel x (mupdateL x st).2 r) :
    (rupdateL x (absR st)).1 = r ∧ (rupdateL x (absR st)).2.1 = absR (mupdateL x st).1 := by
  have hx4 : x.Kind' ≠ W64 4 := by rw [hx]; decide
  have hx1 : x.Kind' ≠ W64 1 := by rw [hx]; decide
  unfold rupdateL
  unfold mupdateL at hrel ⊢
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, absR_items, needsRewriteL,
    absR_rewrites _ hst.1]
  by_cases hf : (lookupL st.items x.Key').2 = true
  · have ha := lookupL_ann st hst x.Key' hf
    simp only [hf, ↓reduceIte, Option.isNone_some, Bool.false_and, Bool.not_true, Bool.false_eq_true,
      Option.getD_some, Bool.true_and, true_and] at hrel ⊢
    generalize (lookupL st.items x.Key').1 = it at ha hrel ⊢
    cases hp : preOkL x it.obj'
    · rw [checkMsgL_preMsgL _ _ hp]
      simp only [hp, Bool.not_false, ↓reduceIte] at hrel ⊢
      simp [RawRel, invalidObjL, invalidOutL] at hrel
      subst hrel; exact ⟨rfl, rfl⟩
    rw [(checkMsgL_none _ _).2 hp]
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
    cases hrj : rejects x.HasReject' x.Reject' it.obj'.Node'
    case true =>
      simp only [hrj, ↓reduceIte] at hrel ⊢
      simp [RawRel, rejectedL, errOutL, hx] at hrel
      subst hrel; exact ⟨rfl, rfl⟩
    simp only [hrj, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
    rw [noop_iff _ _ (updGo_annotated x _)]
    have hua : (updGo x it.obj').Annotated' = false := by rw [updGo_annotated]; exact ha
    have hupd : updatedL x it.obj' = updGo x it.obj' := rfl
    simp only [hupd] at hrel ⊢
    by_cases hw : sameObjL (updGo x it.obj') it.obj' = true ∧ it.canon' = true
    · obtain ⟨hs, hc⟩ := hw
      simp only [hs, hc, and_self, ↓reduceIte, Bool.not_true, Bool.false_eq_true, Bool.and_true,
        Option.getD_none, Bool.not_false] at hrel ⊢
      simp only [RawRel, objOutL, hx4, if_true, if_false] at hrel
      subst hrel
      refine ⟨?_, trivial⟩
      have e := objOfL_objOutL _ ha; simp only [objOutL] at e; rw [e]
    · have hcond : (!(if (!it.canon') = true then some true else none).getD false &&
          sameObjL (updGo x it.obj') it.obj') = false := by
        cases hc : it.canon' <;> cases hs : sameObjL (updGo x it.obj') it.obj' <;> simp_all
      rw [if_neg hw] at hrel ⊢
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      simp only [RawRel, objOutL, hx4, if_true, if_false] at hrel
      subst hrel
      refine ⟨?_, ?_⟩
      · simp only [updWriteL, hua]; rfl
      · rw [absR_set st hst.1 _ rfl]; rfl
  · have hf' : (lookupL st.items x.Key').2 = false := by simpa using hf
    simp only [hf', ↓reduceIte, Option.isNone_none, Bool.true_and, Bool.not_false, Bool.false_eq_true,
      Option.getD_none] at hrel ⊢
    cases hig : x.IgnoreNotFound'
    case false =>
      simp only [hig, Bool.not_false, ↓reduceIte] at hrel ⊢
      simp [RawRel, notFoundL, errOutL] at hrel
      subst hrel; exact ⟨rfl, rfl⟩
    simp only [hig, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
    cases hp : preOkL x zObj
    case false =>
      rw [checkMsgL_preMsgL _ _ hp]
      simp only [hp, Bool.not_false, ↓reduceIte] at hrel ⊢
      simp [RawRel, invalidObjL, invalidOutL] at hrel
      subst hrel; exact ⟨rfl, rfl⟩
    rw [(checkMsgL_none _ _).2 hp]
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
    cases hrj : rejects x.HasReject' x.Reject' zObj.Node'
    case true =>
      simp only [hrj, ↓reduceIte] at hrel ⊢
      simp [RawRel, rejectedL, errOutL, hx] at hrel
      subst hrel; exact ⟨rfl, rfl⟩
    simp only [hrj, Bool.false_eq_true, ↓reduceIte, false_and, and_false] at hrel ⊢
    have hua : (updGo x zObj).Annotated' = false := by rw [updGo_annotated]; rfl
    simp only [RawRel, objOutL, hx4, if_true, if_false] at hrel
    subst hrel
    refine ⟨?_, ?_⟩
    · simp only [updWriteL, hua]; rfl
    · rw [absR_set st hst.1 _ rfl]; rfl

/-- A write's answer never has a too-large or an unknown error (its key accepted). -/
theorem rexecL_write_deep (x : Input) (m : RM)
    (hw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2)
    (hk : keyOkL (storeKeyL x.Key') = true) : ∃ o d, (rexecL x m).1 = ⟨o, .deep d⟩ := by
  have hne4 : x.Kind' ≠ W64 4 := by rcases hw with h | h | h <;> rw [h] <;> decide
  unfold rexecL
  rcases hw with h | h | h
  · rw [if_neg hne4, if_pos h]
    unfold rcreateL
    simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split <;> exact ⟨_, _, rfl⟩
  · have h0 : x.Kind' ≠ W64 0 := by rw [h]; decide
    rw [if_neg hne4, if_neg h0, if_pos h]
    unfold rdeleteL
    simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    repeat' split
    all_goals exact ⟨_, _, rfl⟩
  · have h0 : x.Kind' ≠ W64 0 := by rw [h]; decide
    have h1 : x.Kind' ≠ W64 1 := by rw [h]; decide
    rw [if_neg hne4, if_neg h0, if_neg h1, if_pos h]
    unfold rupdateL updWriteL
    simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    repeat' split
    all_goals exact ⟨_, _, rfl⟩

/-- **B1, a write.** On the abstraction of a driver's store, the maintainers' `Step` accepts a write's real
answer `r`, when `r` is what the driver's output encodes (`RawRel`), and moves to the abstraction of the
driver's next store. Premises: the key is one `PrepareKey` accepts (`keyOkL`), the store is sorted and its
objects not `Annotated` (`StOk`), and its resource version does not wrap. -/
theorem rstepL_write (x : Input) (st : GSt) (r : RResp)
    (hw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2)
    (hk : keyOkL (storeKeyL x.Key') = true) (hst : StOk st)
    (hrel : RawRel x (mstepL x st).2 r) :
    (rstepL x (absR st) r).1 = true ∧ (rstepL x (absR st) r).2.1 = absR (mstepL x st).1 := by
  have hne4 : x.Kind' ≠ W64 4 := by rcases hw with h | h | h <;> rw [h] <;> decide
  have key : (rexecL x (absR st)).1 = r ∧ (rexecL x (absR st)).2.1 = absR (mstepL x st).1 := by
    unfold rexecL mstepL at *
    rcases hw with h | h | h
    · rw [if_pos h] at hrel; rw [if_neg hne4, if_pos h, if_pos h]
      exact rcreateL_absR x st r h hk hst hrel
    · have h0 : x.Kind' ≠ W64 0 := by rw [h]; decide
      rw [if_neg h0, if_pos h] at hrel; rw [if_neg hne4, if_neg h0, if_pos h, if_neg h0, if_pos h]
      exact rdeleteL_absR x st r h hk hst hrel
    · have h0 : x.Kind' ≠ W64 0 := by rw [h]; decide
      have h1 : x.Kind' ≠ W64 1 := by rw [h]; decide
      rw [if_neg h0, if_neg h1, if_pos h] at hrel
      rw [if_neg hne4, if_neg h0, if_neg h1, if_pos h, if_neg h0, if_neg h1, if_pos h]
      exact rupdateL_absR x st r h hk hst hrel
  obtain ⟨o, d, hd⟩ := rexecL_write_deep x (absR st) hw hk
  unfold rstepL
  simp only [hne4, hw, ↓reduceIte, if_true]
  rw [key.1] at hd
  rw [key.1, hd, respEqL_deep]
  exact ⟨rfl, key.2⟩

end go

end k8s_correctness
end EtcdGrove
end Perennial
