/-
Lean-first (no Rocq counterpart).

# The bridge to Kubernetes' checker, B1: one step (k8s 7g step 4)

`notes/k8s-7g-scope.md` §2.3, B1. On the abstraction of a driver's store (`absR`), the maintainers'
`Step` (`rstepL`) accepts the store's own answer to a write (`Raw`, as the checker's `Response`) and lands on
the abstraction of the driver's next store (`mstepL`), when the answer is what the output's plain fields
encode (`RawRel`; stage 7g option (C): a failed precondition's message is a plain field).

- `RawRel x y r` (now in `RawOk.lean`): the plain-field relation of the scope's premise "each output's `Raw` is
  the deep value its plain fields encode" (an object without the `Annotated` bit, a list with non-nil `Items`).
- `absR_items`, `absR_rewrites`, `absR_other`: the abstraction read through `lookupL`.
- `rstepL_write` (B1, writes): `Step` of a write's answer on `absR st` is accepted and moves to
  `absR (mstepL x st).1`.
- `rstepL_get` (B1, gets) and `rstepL_list` (B1, lists: consistent, `Exact`, `NotOlderThan`): `Step` of a
  read's answer, when it is what the driver's answer encodes, is accepted and leaves the state.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RawOk
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

/-! ## B1: a get -/

/-- **B1, a get.** A get's real answer, when it is what the driver's answer at the current store encodes, is
accepted by the maintainers' `Step` (`validateGet` against `execute`'s answer on the same state), which leaves
the state. Premises: the key is accepted, the store sorted and its objects not `Annotated` (`StOk`), its
objects no newer than it (`rmWf`), and its revision positive (the seeded store's). -/
theorem rstepL_get (x : Input) (st : GSt) (r : RResp)
    (hg : ¬ (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2)) (h4 : x.Kind' ≠ W64 4)
    (hk : keyOkL (storeKeyL x.Key') = true) (hst : StOk st) (hwf : rmWf (absR st))
    (hpos : 0 < uint.nat st.rv) (hrel : RawRel x (mgetL x st) r) :
    (rstepL x (absR st) r).1 = true ∧ (rstepL x (absR st) r).2.1 = absR st := by
  unfold rstepL
  rw [if_neg h4, if_neg hg]
  refine ⟨?_, rfl⟩
  have hex : (rexecL x (absR st)).1 = rgetL x (absR st) := by
    unfold rexecL
    simp only [not_or] at hg
    rw [if_neg h4, if_neg hg.1, if_neg hg.2.1, if_neg hg.2.2]
  rw [hex]
  unfold mgetL at hrel
  unfold rgetL
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hp : parseRVD x.MinRV' with
  | none =>
    simp only [hp] at hrel
    simp [RawRel, otherL, errOutL] at hrel
  | some req =>
    simp only [hp] at hrel ⊢
    have hrv : (absR st).rv = st.rv := rfl
    rw [hrv]
    by_cases hlt : uint.nat st.rv < uint.nat req
    · simp only [hlt, if_true] at hrel ⊢
      simp [RawRel, tooLargeL, errOutL] at hrel
      subst hrel
      simp [rvalidateGetL, tooLargeE, isTooLargeE]
    simp only [hlt, if_false] at hrel ⊢
    rw [absR_items]
    by_cases hf : (lookupL st.items x.Key').2 = true
    · have ha := lookupL_ann st hst x.Key' hf
      have hle := hwf.1 (storeKeyL x.Key') (lookupL st.items x.Key').1.obj'
        (by rw [absR_items, if_pos hf])
      simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
      simp only [RawRel, objOutL, h4, if_true, if_false] at hrel
      subst hrel
      have e := objOfL_objOutL _ ha; simp only [objOutL] at e; rw [e]
      unfold rvalidateGetL; by_cases hm : x.MinRV' = [] <;> simp [hm, isTooLargeE, errNonNil, respEqL, delayE, hle]
    · have hf' : (lookupL st.items x.Key').2 = false := by simpa using hf
      simp only [hf', Bool.not_false, ↓reduceIte] at hrel ⊢
      cases hig : x.IgnoreNotFound'
      · simp only [hig, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
        simp [RawRel, notFoundL, errOutL] at hrel
        subst hrel
        have hreq := Nat.le_of_not_lt hlt; unfold rvalidateGetL; by_cases hm : x.MinRV' = [] <;> simp [hm, hp, isTooLargeE, errNonNil, isNotFoundE, respEqL, delayE, notFoundE, hpos, hreq, hrv]
        all_goals rfl
      · simp only [hig, ↓reduceIte] at hrel ⊢
        simp only [RawRel, zeroOutL, errOutL, h4, ↓reduceIte, if_true, if_false] at hrel
        subst hrel
        unfold rvalidateGetL; by_cases hm : x.MinRV' = [] <;> simp [hm, isTooLargeE, errNonNil, respEqL, delayE, objOfL]
        all_goals rfl

/-! ## B1: a list -/

/-- `PrepareKey`'s answer: the key, made a directory if recursive, with the resource prefix. -/
theorem prepareKeyM_some {rp key p : GoString} {r : Bool} (h : k8s.prepareKeyM rp key r = some p) :
    key ≠ [] ∧ p = (if r = true ∧ ¬ go!"/" <:+ key then key ++ go!"/" else key) ∧ rp <+: p := by
  unfold k8s.prepareKeyM at h
  by_cases h1 : k8s.dotDot key = true
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : k8s.dotSeg key = true
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : key = [] ∨ key = go!"/"
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  simp only at h
  by_cases h4 : rp <+: (if r = true ∧ ¬ go!"/" <:+ key then key ++ go!"/" else key)
  · rw [if_pos h4] at h; cases h
    exact ⟨fun e => h3 (.inl e), rfl, h4⟩
  · rw [if_neg h4] at h; cases h

/-- `PrepareKey` with the resource prefix accepts what it accepts without one. -/
theorem prepareKeyM_nil {rp key p : GoString} {r : Bool} (h : k8s.prepareKeyM rp key r = some p) :
    k8s.prepareKeyM [] key r = some p := by
  unfold k8s.prepareKeyM at h ⊢
  by_cases h1 : k8s.dotDot key = true
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h ⊢
  by_cases h2 : k8s.dotSeg key = true
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h ⊢
  by_cases h3 : key = [] ∨ key = go!"/"
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h ⊢
  simp only at h ⊢
  by_cases h4 : rp <+: (if r = true ∧ ¬ go!"/" <:+ key then key ++ go!"/" else key)
  · rw [if_pos h4] at h; rw [if_pos (List.nil_prefix)]; exact h
  · rw [if_neg h4] at h; cases h

theorem trimSufL_append (s suf : GoString) (h : suf <:+ s) : trimSufL s suf ++ suf = s := by
  unfold trimSufL; rw [if_pos h]
  obtain ⟨t, rfl⟩ := h
  simp

/-- The prepared key is a prefix of every key in the list's scope. -/
theorem prepared_scope {rp key p k : GoString} {r : Bool} (hp : k8s.prepareKeyM rp key r = some p)
    (hk : keyInScopeL key r k = true) : p <+: k := by
  obtain ⟨-, rfl, -⟩ := prepareKeyM_some hp
  unfold keyInScopeL at hk
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hk
    subst hk
    simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    exact List.prefix_refl _
  | true =>
    simp only [↓reduceIte, decide_eq_true_eq] at hk
    by_cases hs : go!"/" <:+ key
    · rw [trimSufL_append _ _ hs] at hk
      simp only [hs, not_true_eq_false, and_false, ↓reduceIte]
      exact hk
    · unfold trimSufL at hk
      rw [if_neg hs] at hk
      simp only [hs, not_false_eq_true, and_self, ↓reduceIte]
      exact hk

/-- The prepared key is not empty. -/
theorem prepared_ne {rp key p : GoString} {r : Bool} (hp : k8s.prepareKeyM rp key r = some p) :
    p ≠ [] := by
  obtain ⟨hk, rfl, -⟩ := prepareKeyM_some hp
  split <;> simp_all

/-- What `mlist`'s loop keeps: `hasMore` only past a match, a last key once a match is taken, every
key and item from the items in scope. -/
def LastInv {α O : Type} (P : List α → Prop) (Q : O → Prop) (s : ListModel.LState α O) : Prop :=
  (s.more = true → s.items ≠ []) ∧ (s.items ≠ [] → s.last.isSome) ∧ (∀ k, s.last = some k → P k) ∧
    ∀ o ∈ s.items, Q o

theorem lastInv_foldl {α O : Type} (sel : O → Bool) (limit : Nat) (P : List α → Prop) (Q : O → Prop) :
    ∀ (sc : List (List α × O)) (s : ListModel.LState α O), (∀ ko ∈ sc, P ko.1 ∧ Q ko.2) →
      LastInv P Q s → LastInv P Q (sc.foldl (ListModel.lstep sel limit) s)
  | [], _, _, h => h
  | ko :: sc, s, hP, ⟨h1, h2, h3, h4⟩ => by
    rw [List.foldl_cons]
    apply lastInv_foldl sel limit P Q sc _ (fun k hk => hP k (List.mem_cons_of_mem _ hk))
    have hko := hP ko List.mem_cons_self
    unfold ListModel.lstep
    simp only
    split
    · rename_i hlim
      refine ⟨fun _ he => ?_, h2, h3, h4⟩
      rw [he] at hlim; simp at hlim; omega
    · split
      · refine ⟨fun _ => by simp, fun _ => by simp, ?_, ?_⟩
        · intro k hk; simp only [Option.some.injEq] at hk; subst hk; exact hko.1
        · intro o ho
          rcases List.mem_cons.1 ho with rfl | ho
          · exact hko.2
          · exact h4 o ho
      · exact ⟨h1, h2, h3, h4⟩

theorem lastInv_loop {α O : Type} (sel : O → Bool) (limit : Nat) (P : List α → Prop) (Q : O → Prop)
    (sc : List (List α × O)) (hP : ∀ ko ∈ sc, P ko.1 ∧ Q ko.2) :
    LastInv P Q (ListModel.loop sel limit sc) :=
  lastInv_foldl sel limit P Q sc _ hP ⟨by simp, by simp, by simp, by simp⟩

/-- The driver's loop on a store: its continue token is defined when it has more, its items are the
store's. -/
theorem listLoopL_inv (x : Input) (its : List item) (p : GoString) (rp : GoString)
    (hp : k8s.prepareKeyM rp x.ListKey' x.Recursive' = some p) :
    LastInv (fun k => p <+: k) (fun o => ∃ it ∈ its, it.obj' = o) (listLoopL x its) := by
  apply lastInv_loop
  intro ko hko
  unfold scopeL at hko
  rw [List.mem_filter, List.mem_map] at hko
  obtain ⟨⟨it, hit, rfl⟩, hsc⟩ := hko
  exact ⟨prepared_scope hp hsc, it, hit, rfl⟩

theorem encOkL_loop (x : Input) (its : List item) (p rp : GoString)
    (hp : k8s.prepareKeyM rp x.ListKey' x.Recursive' = some p) (hm : (listLoopL x its).more = true) :
    encOkL ((listLoopL x its).last.getD [] ++ [W8 0]) p = true := by
  obtain ⟨h1, h2, h3, -⟩ := listLoopL_inv x its p rp hp
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (h2 (h1 hm))
  rw [hk]
  unfold encOkL
  simp only [Option.getD_some, decide_eq_true_eq]
  exact ⟨prepared_ne hp, (h3 k hk).trans (List.prefix_append _ _)⟩

/-- The model's and the driver's continue tokens: the store's prefix `/registry` on both sides. -/
theorem encOkL_reg (a b : GoString) (hb : b ≠ []) :
    encOkL (go!"/registry" ++ a) (go!"/registry" ++ b) = encOkL a b := by
  unfold encOkL; simp [hb]

theorem encL_reg (a b : GoString) (rv : w64) :
    encL (go!"/registry" ++ a) (go!"/registry" ++ b) rv = encL a b rv := by
  unfold encL
  rw [List.length_append, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _),
    List.nil_append, Nat.add_sub_cancel_left]

theorem scopeR_absR (x : Input) (st : GSt) (hs : SortedI st.items) :
    scopeR x.ListKey' x.Recursive' (absR st) = scopeL x st.items := by
  unfold scopeR scopeL; rw [itemsL_absR st hs]

theorem absR_rv (st : GSt) : (absR st).rv = st.rv := rfl

theorem parseRVD_nil : parseRVD [] = some 0 := by simp [parseRVD]

/-- `ListReadConsistency`'s resource version is the one `parseRV` reads. -/
theorem listConsL_parse (x : Input) (c : RCons) (rq : w64) (h : listConsL x = some (c, rq)) :
    parseRVD x.MinRV' = some rq := by
  unfold listConsL at h
  by_cases hm : x.MinRV' = []
  · rw [if_pos hm] at h; rw [hm, parseRVD_nil]
    split at h
    · cases h
    · cases h; rfl
  · rw [if_neg hm] at h
    cases hp : parseRVD x.MinRV' with
    | none => rw [hp] at h; cases h
    | some rv =>
      rw [hp] at h; simp only at h
      (repeat' split at h) <;> simp_all

theorem w64_z : (W64 0 : w64) = 0 := rfl
theorem w64_ne_01 : (W64 0 : w64) ≠ W64 1 := by decide
theorem w64_ne_02 : (W64 0 : w64) ≠ W64 2 := by decide
theorem w64_ne_12 : (W64 1 : w64) ≠ W64 2 := by decide

/-- **The driver reads a past store exactly when the checker's read is `Exact`** (for the matches the
driver draws, `0`, `1`, `2`), and then at a positive resource version. -/
theorem listConsL_past (x : Input) (c : RCons) (rq : w64)
    (hm : x.Match' = W64 0 ∨ x.Match' = W64 1 ∨ x.Match' = W64 2) (h : listConsL x = some (c, rq)) :
    (pastReadL x rq = true ↔ c = .exact) ∧ (c = .exact → rq ≠ 0) := by
  unfold listConsL at h
  unfold pastReadL
  by_cases hmv : x.MinRV' = []
  · rw [if_pos hmv] at h
    split at h
    · cases h
    · cases h; simp [hmv]
  · rw [if_neg hmv] at h
    cases hp : parseRVD x.MinRV' with
    | none => rw [hp] at h; cases h
    | some rv =>
      rw [hp] at h; simp only at h
      rcases hm with e | e | e
      · rw [e, if_neg w64_ne_01, if_neg w64_ne_02] at h
        rw [e]
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          rw [if_neg (fun hh => hh.elim hmv (fun e => hc.2 e))]
          exact ⟨by simp [hc.1.1, hc.1.2], fun _ => hc.2⟩
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hc
          by_cases h0 : rq = 0
          · subst h0; simp [w64_z]
          · rw [if_neg (fun hh => hh.elim hmv (fun e => h0 e))]
            refine ⟨?_, by simp⟩
            simp only [w64_ne_02, decide_false, Bool.false_or, decide_true, Bool.true_and,
              reduceCtorEq, iff_false, Bool.and_eq_true, decide_eq_true_eq]
            exact fun hh => hc hh h0
      · rw [e, if_pos rfl] at h
        cases h
        rw [e]
        simp [hmv, w64_ne_12.symm, w64_ne_01.symm]
      · rw [e, if_neg w64_ne_12.symm, if_pos rfl] at h
        split at h
        · cases h
        · rename_i h0
          cases h
          rw [e, if_neg (fun hh => hh.elim hmv (fun e => h0 e))]
          exact ⟨by simp, fun _ => h0⟩

/-- **The checker's list on the current store's abstraction** (no error): the driver's loop on the
store, its items, revision, and its continue token and remaining count if it has more. -/
theorem rlistL_cur (x : Input) (st : GSt) (p : GoString) (c : RCons) (rq : w64)
    (hp : k8s.prepareKeyM [] x.ListKey' x.Recursive' = some p) (hc : listConsL x = some (c, rq))
    (hle : ¬ uint.nat st.rv < uint.nat rq) (hs : SortedI st.items) :
    rlistL x (absR st) =
      if (listLoopL x st.items).more then
        ⟨.list (some (listLoopL x st.items).items.reverse) st.rv
          (encL ((listLoopL x st.items).last.getD [] ++ [W8 0]) p st.rv)
          (if predEmptyL x then some (W64 ((listLoopL x st.items).total : Int) - x.Limit') else none),
          .none⟩
      else ⟨.list (some (listLoopL x st.items).items.reverse) st.rv [] none, .none⟩ := by
  unfold rlistL
  simp only [hp, hc]
  rw [if_neg (show ¬ uint.nat (absR st).rv < uint.nat rq from hle), scopeR_absR x st hs,
    show ListModel.loop (selOkL x) (limitN x) (scopeL x st.items) = listLoopL x st.items from rfl]
  by_cases hm : (listLoopL x st.items).more = true
  · simp only [hm, ↓reduceIte, encOkL_loop x st.items p [] hp hm]; rfl
  · have hm' : (listLoopL x st.items).more = false := by simpa using hm
    simp only [hm', Bool.false_eq_true, ↓reduceIte]; rfl

/-- **What the driver's list answer encodes**: a list of objects with the answer's items, at the store's
revision, with the continue token and remaining count it has. -/
theorem rawRel_listOutL (x : Input) (st : GSt) (p : GoString) (r : RResp) (h4 : x.Kind' = W64 4)
    (hrel : RawRel x (listOutL x st (listLoopL x st.items) p) r) :
    ∃ its, (∀ o ∈ its, itemOk o) ∧ encItemsL its = encItemsL (listLoopL x st.items).items.reverse ∧
      r = if (listLoopL x st.items).more then
        ⟨.list (some its) st.rv
          (encL ((listLoopL x st.items).last.getD [] ++ [W8 0]) p st.rv)
          (if predEmptyL x then some (W64 ((listLoopL x st.items).total : Int) - x.Limit') else none),
          .none⟩
      else ⟨.list (some its) st.rv [] none, .none⟩ := by
  unfold listOutL at hrel
  simp only at hrel
  by_cases hm : (listLoopL x st.items).more = true
  · rw [if_pos hm] at hrel
    simp only [hm, ↓reduceIte]
    by_cases he : encOkL (go!"/registry" ++ (listLoopL x st.items).last.getD [] ++ [W8 0])
        (go!"/registry" ++ p) = true
    · rw [if_pos he] at hrel
      simp only [RawRel, h4, ↓reduceIte] at hrel
      obtain ⟨its, hio, hits, hr⟩ := hrel
      refine ⟨its, hio, hits.symm, ?_⟩
      rw [hr]
      simp only [List.append_assoc, encL_reg]
      by_cases hpe : predEmptyL x = true <;> simp [hpe]
    · rw [if_neg he] at hrel
      simp [RawRel, otherL, errOutL] at hrel
  · rw [if_neg hm] at hrel
    have hm' : (listLoopL x st.items).more = false := by simpa using hm
    simp only [hm', Bool.false_eq_true, ↓reduceIte]
    simp only [RawRel, h4, ↓reduceIte] at hrel
    obtain ⟨its, hio, hits, hr⟩ := hrel
    exact ⟨its, hio, hits.symm, by rw [hr]; simp⟩

/-- **B1, a list.** A list's real answer, when it is what the driver's answer (`mlistL`, at the store it
reads: the current one, or the history's at the requested revision for an `Exact` read) encodes, is accepted
by the maintainers' `Step` (`validateList` against `execute`'s answer on the current state), which leaves the
state: a too-large error for both; a consistent read the same list (the store's key order is the checker's);
an `Exact` read a list at the requested revision (the history's store there has that revision); a
`NotOlderThan` read a list at the current revision. Premises: the match is one the driver draws and
`ListReadConsistency` accepts the options, `PrepareKey` accepts the key, the store is sorted, its objects not
`Annotated` (`StOk`) and ones `encodeItems` is injective on (`itemOk`), its revision positive, and the
history's store at each revision up to the current one has that revision. -/
theorem rstepL_list (x : Input) (h : HSt) (r : RResp) (h4 : x.Kind' = W64 4)
    (hm : x.Match' = W64 0 ∨ x.Match' = W64 1 ∨ x.Match' = W64 2) (hcons : (listConsL x).isSome)
    (hkey : (k8s.prepareKeyM [] x.ListKey' x.Recursive').isSome)
    (hst : StOk h.st) (hio : ∀ it ∈ h.st.items, itemOk it.obj') (hpos : 0 < uint.nat h.st.rv)
    (hhist : ∀ q : w64, 0 < uint.nat q → uint.nat q ≤ uint.nat h.st.rv → (histAtL h.hist q).rv = q)
    (hrel : RawRel x (mlistL x h) r) :
    (rstepL x (absR h.st) r).1 = true ∧ (rstepL x (absR h.st) r).2.1 = absR h.st := by
  unfold rstepL
  rw [if_pos h4]
  refine ⟨?_, rfl⟩
  have hex : (rexecL x (absR h.st)).1 = rlistL x (absR h.st) := by unfold rexecL; rw [if_pos h4]
  rw [hex]
  obtain ⟨⟨c, rq⟩, hc⟩ := Option.isSome_iff_exists.1 hcons
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hkey
  have hparse := listConsL_parse x c rq hc
  obtain ⟨hpast, hex0⟩ := listConsL_past x c rq hm hc
  unfold mlistL at hrel
  rw [hparse] at hrel
  simp only at hrel
  by_cases hlt : uint.nat h.st.rv < uint.nat rq
  · rw [if_pos hlt] at hrel
    simp [RawRel, tooLargeL, errOutL] at hrel
    subst hrel
    have e : rlistL x (absR h.st) = ⟨.nil, tooLargeE⟩ := by
      unfold rlistL; simp only [hp, hc]; rw [if_pos (show uint.nat (absR h.st).rv < uint.nat rq from hlt)]
    rw [e]; simp [rvalidateListL, tooLargeE, isTooLargeE]
  rw [if_neg hlt] at hrel
  cases hpo : k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive' with
  | none => rw [hpo] at hrel; simp [RawRel, otherL, errOutL] at hrel
  | some p' =>
    rw [hpo] at hrel; simp only at hrel
    have hpp : p = p' := by
      have e := prepareKeyM_nil hpo; rw [hp] at e; exact Option.some.inj e
    subst hpp
    have hE : (rlistL x (absR h.st)).err = .none := by
      rw [rlistL_cur x h.st p c rq hp hc hlt hst.1]; split <;> rfl
    unfold rvalidateListL
    rw [if_neg (by rw [hE]; simp [isTooLargeE]), if_neg (by rw [hE]; simp [errNonNil]), hc]
    simp only
    cases c with
    | exact =>
      have hrq0 := hex0 rfl
      have hpr : pastReadL x rq = true := hpast.2 rfl
      unfold listStL at hrel
      rw [if_pos hpr] at hrel
      have hrv : (histAtL h.hist rq).rv = rq := hhist rq
        (by rcases Nat.eq_zero_or_pos (uint.nat rq) with e | e
            · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using e) hrq0
            · exact e)
        (Nat.le_of_not_lt hlt)
      obtain ⟨its, -, -, hr⟩ := rawRel_listOutL x _ p r h4 hrel
      have hlr : listRespRVL r = some rq := by
        rw [hr]; split <;> simp [listRespRVL, errNonNil, hrv] <;> exact hrq0
      rw [hlr]
      have hd : delayE r.err = false := by rw [hr]; split <;> rfl
      simp [hd]
    | notOlderThan =>
      have hpr : pastReadL x rq = false := by
        cases e : pastReadL x rq
        · rfl
        · cases hpast.1 e
      unfold listStL at hrel
      rw [if_neg (by simp [hpr])] at hrel
      have hne : h.st.rv ≠ 0 := by intro e; rw [e] at hpos; simp at hpos
      obtain ⟨its, -, -, hr⟩ := rawRel_listOutL x _ p r h4 hrel
      have hlr : listRespRVL r = some h.st.rv := by
        rw [hr]; split <;> simp [listRespRVL, errNonNil] <;> exact hne
      rw [hlr]
      have hd : delayE r.err = false := by rw [hr]; split <;> rfl
      simp [hd, absR_rv, Nat.le_of_not_lt hlt]
    | consistent =>
      have hpr : pastReadL x rq = false := by
        cases e : pastReadL x rq
        · rfl
        · cases hpast.1 e
      unfold listStL at hrel
      rw [if_neg (by simp [hpr])] at hrel
      obtain ⟨its, hio', hits, hr⟩ := rawRel_listOutL x _ p r h4 hrel
      have hii : its = (listLoopL x h.st.items).items.reverse := by
        apply encItemsL_inj _ _ hio' _ hits
        intro o ho
        obtain ⟨-, -, -, h4'⟩ := listLoopL_inv x h.st.items p [] hp
        obtain ⟨it, hit, rfl⟩ := h4' o (List.mem_reverse.1 ho)
        exact hio it hit
      subst hii
      have hd : delayE r.err = false := by rw [hr]; split <;> rfl
      simp only [hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      unfold equalListRespL
      rw [rlistL_cur x h.st p .consistent rq hp hc hlt hst.1, hr]
      split <;> simp [respEqL]

end go

end k8s_correctness
end EtcdGrove
end Perennial
