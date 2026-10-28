/-
Lean-first (no Rocq counterpart).

# The store's model refines the driver's (stage 6b of `notes/k8s-etcd3-plan.md`)

The store's specs answer in terms of `Model.lean`'s `KSt` (items by etcd key, resource versions
as numbers); the driver's model (`KModel.lean`'s `mstepL`) computes on `mstore`s (items sorted
by name, 64-bit resource versions). `KRel ks g` relates them: the same resource version, and at
every name `n`, the store's item at the etcd key `mkeyL n` (`"/registry/objs/" ++ n`) is `g`'s
item of `n` (`ItemRel`: its object's name and value, its resource version, its canonical bit).

`outOf r` is the driver's `Output` of the store's answer `r` (`call`: `objOut` of the object, an
`errOut` of the error; a callback's error is `ERejected`). For each operation, on related states,
the store's model and the driver's answer the same and stay related (`refine_create`,
`refine_delete`, `refine_update`, `refine_get`), given the next resource version fits 64 bits.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.ItemList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open k8s
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item)

section go
variable [GooseExts]

/-- A store item and a driver item agree. -/
def ItemRel (ki : KItem DObj) (it : item) : Prop :=
  ki.obj.1 = (it.obj'.Name', it.obj'.Value') ∧ W64 (ki.rv : Int) = it.obj'.ResourceVersion' ∧
    ki.canon = it.canon'

/-- A store item and `lookupL`'s answer agree (both absent, or both present and related). -/
def PairRel : Option (KItem DObj) → item × Bool → Prop
  | none, (_, false) => True
  | some ki, (it, true) => ItemRel ki it
  | _, _ => False

/-- **The store's state and the driver's** (see the file header). -/
def KRel (ks : KSt DObj) (g : GSt) : Prop :=
  SortedI g.items ∧ W64 (ks.rv : Int) = g.rv ∧ ks.rv < 2 ^ 64 ∧
    ∀ n, PairRel (ks.items (mkeyL n)) (lookupL g.items n)

/-- **The driver's output of a store answer** (`call`'s `objOut`/`errOut`). -/
def outOf {E : Type} : KResp DObj E → Output
  | .obj o rv => objOutL ⟨o.1.1, o.1.2, W64 (rv : Int)⟩
  | .zero => zeroOutL
  | .err (.notFound k rv) => ⟨W64 1, k, W64 (rv : Int), [], [], 0⟩
  | .err (.keyExists k) => ⟨W64 2, k, W64 0, [], [], 0⟩
  | .err (.user _) => rejectedL
  | .err _ => ⟨W64 4, [], 0, [], [], 0⟩

theorem mkeyL_inj {a b : GoString} (h : mkeyL a = mkeyL b) : a = b := by
  unfold mkeyL storeKeyL at h
  simpa using h

/-- `lookupL`'s found item has the key. -/
theorem lookupL_key (its : List item) (n : GoString) (it : item)
    (h : lookupL its n = (it, true)) : it.key' = n := by
  unfold lookupL at h
  split at h
  · next e he =>
    have := List.find?_some he
    simp only [decide_eq_true_eq] at this
    simp only [Prod.mk.injEq] at h
    rw [← h.1]; exact this
  · simp at h

theorem w64_succ (r : Nat) (h : r + 1 < 2 ^ 64) :
    W64 ((r + 1 : Nat) : Int) = W64 (r : Int) + W64 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [W64, BitVec.toNat_ofInt, BitVec.toNat_add]
  omega

/-- The related states at the name `n`: both absent. -/
theorem krel_none {ks : KSt DObj} {g : GSt} (h : KRel ks g) (n : GoString)
    (hn : ks.items (mkeyL n) = none) : (lookupL g.items n).2 = false := by
  have := h.2.2.2 n
  rw [hn] at this
  revert this
  rcases lookupL g.items n with ⟨it, b⟩
  cases b <;> simp [PairRel]

/-- The related states at the name `n`: both present. -/
theorem krel_some {ks : KSt DObj} {g : GSt} (h : KRel ks g) (n : GoString) (ki : KItem DObj)
    (hn : ks.items (mkeyL n) = some ki) :
    (lookupL g.items n).2 = true ∧ ItemRel ki (lookupL g.items n).1 := by
  have := h.2.2.2 n
  rw [hn] at this
  revert this
  rcases lookupL g.items n with ⟨it, b⟩
  cases b <;> simp [PairRel]

/-- A write at `key` keeps the relation elsewhere and relates the new item. -/
theorem krel_set (ks : KSt DObj) (g : GSt) (h : KRel ks g) (key : GoString) (ki : KItem DObj)
    (it : item) (hk : it.key' = key) (hr : ItemRel ki it) (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel ⟨ks.setItem (mkeyL key) ki, ks.rv + 1⟩ ⟨setItemL g.items it, g.rv + W64 1⟩ := by
  obtain ⟨hs, hrv0, -, hall⟩ := h
  refine ⟨sortedI_setItemL _ _ hs, ?_, hrv, ?_⟩
  · show W64 ((ks.rv + 1 : Nat) : Int) = g.rv + W64 1
    rw [w64_succ _ hrv, hrv0]
  · intro n
    simp only [KSt.setItem]
    rw [lookupL_setItemL _ _ hs]
    by_cases hn : n = key
    · subst hn; simp [hk, PairRel, hr]
    · have h1 : mkeyL n ≠ mkeyL key := fun he => hn (mkeyL_inj he)
      have h2 : it.key' ≠ n := fun he => hn (he ▸ hk ▸ rfl)
      rw [if_neg h1, if_neg h2]
      exact hall n

/-- A deletion at `key` keeps the relation elsewhere. -/
theorem krel_del (ks : KSt DObj) (g : GSt) (h : KRel ks g) (key : GoString)
    (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel ⟨ks.delItem (mkeyL key), ks.rv + 1⟩ ⟨delItemL g.items key, g.rv + W64 1⟩ := by
  obtain ⟨hs, hrv0, -, hall⟩ := h
  refine ⟨sortedI_delItemL _ _ hs, ?_, hrv, ?_⟩
  · show W64 ((ks.rv + 1 : Nat) : Int) = g.rv + W64 1
    rw [w64_succ _ hrv, hrv0]
  · intro n
    simp only [KSt.delItem]
    rw [lookupL_delItemL]
    by_cases hn : key = n
    · subst hn; simp [PairRel]
    · have h1 : mkeyL n ≠ mkeyL key := fun he => hn (mkeyL_inj he).symm
      rw [if_neg h1, if_neg hn]
      exact hall n

/-! ## The operations -/

/-- **`Create`** of the input's name and value (no resource version). -/
theorem refine_create {E : Type} (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input)
    (hlen : x.Key'.length < 256) (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (ks.create (E := E) (mkeyL x.Key') ⟨(x.Key', x.Val'), hlen⟩ 0).1
        (mcreateL x g).1 ∧
      outOf (ks.create (E := E) (mkeyL x.Key') ⟨(x.Key', x.Val'), hlen⟩ 0).2 =
        (mcreateL x g).2 := by
  unfold KSt.create mcreateL
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  cases hk : ks.items (mkeyL x.Key') with
  | some ki =>
    have := (krel_some h _ ki hk).1
    simp only [this, ↓reduceIte]
    exact ⟨h, rfl⟩
  | none =>
    have hn := krel_none h _ hk
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    refine ⟨krel_set ks g h x.Key' _ _ rfl ⟨rfl, ?_, rfl⟩ hrv, ?_⟩
    · show W64 ((ks.rv + 1 : Nat) : Int) = g.rv + W64 1
      rw [w64_succ _ hrv, h.2.1]
    · simp only [outOf]
      rw [w64_succ _ hrv, h.2.1]

/-- An object's driver form: `ItemRel`'s object. -/
theorem itemRel_obj {ki : KItem DObj} {it : item} (h : ItemRel ki it) :
    (⟨ki.obj.1.1, ki.obj.1.2, W64 (ki.rv : Int)⟩ : Obj) = it.obj' := by
  obtain ⟨h1, h2, -⟩ := h
  rw [h1, h2]

/-- **`Delete`** of the input's name, `validateFor(in.Reject)` rejecting with `eD`. -/
theorem refine_delete (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input) (eD : GoInterface)
    (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (ks.delete (mkeyL x.Key') (fun _ _ => none) (rejD eD x.Reject')).1 (mdeleteL x g).1 ∧
      outOf (ks.delete (mkeyL x.Key') (fun _ _ => none) (rejD eD x.Reject')).2 =
        (mdeleteL x g).2 := by
  unfold KSt.delete mdeleteL
  cases hk : ks.items (mkeyL x.Key') with
  | none =>
    have hn := krel_none h _ hk
    simp only [hn, Bool.not_false, ↓reduceIte]
    refine ⟨h, ?_⟩
    simp only [outOf, notFoundL, h.2.1]
  | some ki =>
    obtain ⟨hf, hr⟩ := krel_some h _ ki hk
    simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, rejD]
    have hv : ki.obj.1.2 = (lookupL g.items x.Key').1.obj'.Value' := by rw [hr.1]
    rw [hv]
    cases hrj : rejects x.Reject' (lookupL g.items x.Key').1.obj'.Value'
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨krel_del ks g h x.Key' hrv, ?_⟩
      simp only [outOf, objOutL]
      rw [w64_succ _ hrv, h.2.1, hr.1]
    · simp only [↓reduceIte]
      exact ⟨h, rfl⟩

/-- **`GuaranteedUpdate`** of the input's name by `tryUpdateFor(in)` (rejecting with `eU`; no
`ignoreNotFound`, no preconditions). -/
theorem refine_update (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input) (eU : GoInterface)
    (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (ks.update (mkeyL x.Key') false dzero (fun _ _ => none) (updD eU x)).1 (mupdateL x g).1 ∧
      outOf (ks.update (mkeyL x.Key') false dzero (fun _ _ => none) (updD eU x)).2 =
        (mupdateL x g).2 := by
  unfold KSt.update KSt.current mupdateL
  cases hk : ks.items (mkeyL x.Key') with
  | none =>
    have hn := krel_none h _ hk
    simp only [hn, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨h, ?_⟩
    simp only [outOf, notFoundL, h.2.1]
  | some ki =>
    obtain ⟨hf, hr⟩ := krel_some h _ ki hk
    simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, updD]
    have hv : ki.obj.1.2 = (lookupL g.items x.Key').1.obj'.Value' := by rw [hr.1]
    rw [hv]
    cases hrj : rejects x.Reject' (lookupL g.items x.Key').1.obj'.Value'
    · simp only [Bool.false_eq_true, ↓reduceIte, updatedL]
      generalize hit : (lookupL g.items x.Key').1 = it at hr hv
      have hk' : it.key' = x.Key' := lookupL_key g.items x.Key' it (by rw [← hit, ← hf])
      by_cases hsame : (if x.NoOp' = true then it.obj'.Value' else x.Val') = it.obj'.Value' ∧
          it.canon' = true
      · have hobj : updObj x ki.obj = ki.obj := by
          apply Subtype.ext
          simp only [updObj, hr.1, hsame.1]
        have hc : ki.canon = true := hr.2.2.trans hsame.2
        simp only [hobj, hc, and_self, ↓reduceIte, hsame, true_and]
        refine ⟨h, ?_⟩
        simp only [outOf]
        rw [itemRel_obj hr]
      · have hne : ¬ (updObj x ki.obj = ki.obj ∧ ki.canon = true) := by
          rintro ⟨h1, h2⟩
          apply hsame
          have h1' := congrArg (fun o : DObj => o.1.2) h1
          simp only [updObj, hr.1] at h1'
          exact ⟨h1', hr.2.2 ▸ h2⟩
        simp only [hne, ↓reduceIte, true_and, hsame]
        refine ⟨krel_set ks g h x.Key' _ _ rfl ⟨?_, ?_, rfl⟩ hrv, ?_⟩
        · simp only [updObj, hr.1]
        · show W64 ((ks.rv + 1 : Nat) : Int) = g.rv + W64 1
          rw [w64_succ _ hrv, h.2.1]
        · simp only [outOf, objOutL, updObj, hr.1]
          rw [w64_succ _ hrv, h.2.1]
    · simp only [↓reduceIte]
      exact ⟨h, rfl⟩

/-- **`Get`** of the input's name (no resource version; `ignoreNotFound` as given). -/
theorem refine_get {E : Type} (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input) :
    outOf (ks.get (E := E) (mkeyL x.Key') 0 x.IgnoreNotFound') = mgetL x g := by
  unfold KSt.get mgetL
  simp only [gt_iff_lt, Nat.not_lt_zero, ↓reduceIte]
  cases hk : ks.items (mkeyL x.Key') with
  | none =>
    have hn := krel_none h _ hk
    simp only [hn, Bool.not_false, ↓reduceIte]
    cases x.IgnoreNotFound'
    · simp only [Bool.false_eq_true, ↓reduceIte, outOf, notFoundL, h.2.1]
    · rfl
  | some ki =>
    obtain ⟨hf, hr⟩ := krel_some h _ ki hk
    simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, outOf]
    rw [itemRel_obj hr]

end go

end k8setcd3
end EtcdGrove
end Perennial
