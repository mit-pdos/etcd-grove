/-
Lean-first (no Rocq counterpart).

# The store's model refines the driver's (stage 6b of `notes/k8s-etcd3-plan.md`)

The store's specs answer in terms of `Model.lean`'s `KSt` (items by etcd key, resource versions
as numbers); the driver's model (`KModel.lean`'s `mstepL`) computes on `mstore`s (items sorted
by name, 64-bit resource versions). `KRel ks g` relates them: the same resource version, and at
every name `n`, the store's item at the etcd key `mkeyL n` (`"/registry/objs/" ++ n`) is `g`'s
item of `n` (`ItemRel`: its object's name, UID and value, its resource version, its canonical
bit).

`outOf r` is the driver's `Output` of the store's answer `r` (`call`: `objOut` of the object, an
`errOut` of the error; a callback's error is `ERejected`). For each operation, on related states,
the store's model and the driver's answer the same and stay related (`refine_create`,
`refine_delete`, `refine_update`, `refine_get`), given the next resource version fits 64 bits.
Stage 7b: the input's preconditions (`kpreOf`, the store's `preOk`), updates with
`ignoreNotFound` (from `dzero`), and a `Get`'s minimum resource version.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ItemList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section go
variable [GooseExts]

/-- A store item and a driver item agree. -/
def ItemRel (ki : KItem DObj) (it : item) : Prop :=
  ki.obj.1 = (it.obj'.Name', it.obj'.UID', it.obj'.Value') ∧
    W64 (ki.rv : Int) = it.obj'.ResourceVersion' ∧
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
  | .obj o rv => objOutL ⟨o.name, o.uid, o.val, W64 (rv : Int)⟩
  | .zero => zeroOutL
  | .err (.notFound k rv) => ⟨W64 1, k, W64 (rv : Int), [], [], [], 0⟩
  | .err (.keyExists k) => ⟨W64 2, k, W64 0, [], [], [], 0⟩
  | .err (.invalidObj k) => ⟨W64 5, k, W64 0, [], [], [], 0⟩
  | .err (.user _) => rejectedL
  | .err _ => otherL

/-- **The store's preconditions of an input** (`preconditions(in)`, stage 7b): the UID and the
resource version's string, where given. -/
def kpreOf (x : Input) : KPre :=
  ⟨if x.HasPreUID' then some x.PreUID' else none, if x.HasPreRV' then some x.PreRV' else none⟩

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

/-- **`Create`** of the input's name, UID and value (no resource version). -/
theorem refine_create {E : Type} (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input)
    (hlen : x.Key'.length < 256 ∧ x.UID'.length < 256) (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (ks.create (E := E) (mkeyL x.Key') ⟨(x.Key', x.UID', x.Val'), hlen⟩ 0).1
        (mcreateL x g).1 ∧
      outOf (ks.create (E := E) (mkeyL x.Key') ⟨(x.Key', x.UID', x.Val'), hlen⟩ 0).2 =
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
    (⟨ki.obj.name, ki.obj.uid, ki.obj.val, W64 (ki.rv : Int)⟩ : Obj) = it.obj' := by
  obtain ⟨h1, h2, -⟩ := h
  have e : ki.obj.1 = (ki.obj.name, ki.obj.uid, ki.obj.val) := rfl
  rw [e] at h1
  simp only [Prod.mk.injEq] at h1
  rw [h1.1, h1.2.1, h1.2.2, h2]

/-- **The store's preconditions are the driver's** (`preOk`) on related objects. -/
theorem preOk_rel (x : Input) (ki : KItem DObj) (it : item) (h : ItemRel ki it) :
    driverCodec.preOk (kpreOf x) ki.obj ki.rv = preOkL x it.obj' := by
  obtain ⟨h1, h2, -⟩ := h
  have hu : ki.obj.uid = it.obj'.UID' := congrArg (fun p => p.2.1) h1
  simp only [ObjCodec.preOk, driverCodec, KPre.ok, kpreOf, preOkL, hu, h2]
  cases x.HasPreUID' <;> cases x.HasPreRV' <;> simp

/-- **`Delete`** of the input's name, with the input's preconditions (`kpreOf`) and
`validateFor(in.Reject)` rejecting with `eD`. -/
theorem refine_delete (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input) (eD : GoInterface)
    (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (ks.delete (mkeyL x.Key') (driverCodec.preOk (kpreOf x)) (rejD eD x.Reject')).1
        (mdeleteL x g).1 ∧
      outOf (ks.delete (mkeyL x.Key') (driverCodec.preOk (kpreOf x)) (rejD eD x.Reject')).2 =
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
    rw [preOk_rel x ki _ hr]
    cases hp : preOkL x (lookupL g.items x.Key').1.obj'
    · simp only [Bool.not_false, ↓reduceIte]
      exact ⟨h, rfl⟩
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hn1 : ki.obj.name = (lookupL g.items x.Key').1.obj'.Name' := congrArg (fun p => p.1) hr.1
    have hu1 : ki.obj.uid = (lookupL g.items x.Key').1.obj'.UID' :=
      congrArg (fun p => p.2.1) hr.1
    have hv : ki.obj.val = (lookupL g.items x.Key').1.obj'.Value' := congrArg (fun p => p.2.2) hr.1
    rw [hv]
    cases hrj : rejects x.Reject' (lookupL g.items x.Key').1.obj'.Value'
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨krel_del ks g h x.Key' hrv, ?_⟩
      simp only [outOf, objOutL, hn1, hu1, hv]
      rw [w64_succ _ hrv, h.2.1]
    · simp only [↓reduceIte]
      exact ⟨h, rfl⟩

/-- `updObj` and `updatedL` agree on objects that do. -/
theorem updObj_rel (x : Input) (hlen : x.Key'.length < 256) (o : DObj) (O : Obj)
    (ho : o.1 = (O.Name', O.UID', O.Value')) :
    (updObj x o).1 = ((updatedL x O).Name', (updatedL x O).UID', (updatedL x O).Value') := by
  obtain ⟨h1, h2, h3⟩ := updObj_fields x o hlen
  have hn : o.name = O.Name' := congrArg (fun p => p.1) ho
  have hu : o.uid = O.UID' := congrArg (fun p => p.2.1) ho
  have hv : o.val = O.Value' := congrArg (fun p => p.2.2) ho
  show ((updObj x o).name, (updObj x o).uid, (updObj x o).val) = _
  rw [h1, h2, h3, hn, hu, hv]
  unfold updatedL
  cases x.NoOp' <;> simp

/-- An update's write: the relation kept, the answers alike. -/
theorem upd_write {E : Type} (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input)
    (hlen : x.Key'.length < 256) (hrv : ks.rv + 1 < 2 ^ 64) (o : DObj) (O : Obj)
    (ho : o.1 = (O.Name', O.UID', O.Value')) :
    KRel ⟨ks.setItem (mkeyL x.Key') ⟨updObj x o, ks.rv + 1, true⟩, ks.rv + 1⟩
        ⟨setItemL g.items ⟨x.Key', ⟨(updatedL x O).Name', (updatedL x O).UID', (updatedL x O).Value',
          g.rv + W64 1⟩, true⟩, g.rv + W64 1⟩ ∧
      outOf (E := E) (.obj (updObj x o) (ks.rv + 1)) =
        objOutL ⟨(updatedL x O).Name', (updatedL x O).UID', (updatedL x O).Value', g.rv + W64 1⟩ := by
  have hu := updObj_rel x hlen o O ho
  have hw : W64 ((ks.rv + 1 : Nat) : Int) = g.rv + W64 1 := by rw [w64_succ _ hrv, h.2.1]
  refine ⟨krel_set ks g h x.Key' _ _ rfl ⟨hu, hw, rfl⟩ hrv, ?_⟩
  have h1 : (updObj x o).name = (updatedL x O).Name' := congrArg (fun p => p.1) hu
  have h2 : (updObj x o).uid = (updatedL x O).UID' := congrArg (fun p => p.2.1) hu
  have h3 : (updObj x o).val = (updatedL x O).Value' := congrArg (fun p => p.2.2) hu
  simp only [outOf, h1, h2, h3, hw]

/-- **`GuaranteedUpdate`** of the input's name by `tryUpdateFor(in)` (rejecting with `eU`), with
the input's preconditions (`kpreOf`) and `ignoreNotFound` (from the zero object `dzero`, which
`updated` names `in.Key`). -/
theorem refine_update (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input) (eU : GoInterface)
    (hlen : x.Key'.length < 256) (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (ks.update (mkeyL x.Key') x.IgnoreNotFound' dzero (driverCodec.preOk (kpreOf x))
        (updD eU x)).1 (mupdateL x g).1 ∧
      outOf (ks.update (mkeyL x.Key') x.IgnoreNotFound' dzero (driverCodec.preOk (kpreOf x))
        (updD eU x)).2 = (mupdateL x g).2 := by
  unfold KSt.update KSt.current mupdateL
  cases hk : ks.items (mkeyL x.Key') with
  | none =>
    have hn := krel_none h _ hk
    cases hi : x.IgnoreNotFound'
    · simp only [hn, hi, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
      refine ⟨h, ?_⟩
      simp only [outOf, notFoundL, h.2.1]
    · simp only [hn, hi, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]
      have hpz : driverCodec.preOk (kpreOf x) dzero 0 = preOkL x zObj :=
        preOk_rel x ⟨dzero, 0, true⟩ ⟨x.Key', zObj, true⟩ ⟨rfl, rfl, rfl⟩
      rw [hpz]
      cases hp : preOkL x zObj
      · simp only [Bool.not_false, ↓reduceIte]
        exact ⟨h, rfl⟩
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, updD]
      rw [show dzero.val = zObj.Value' from rfl]
      cases hrj : rejects x.Reject' zObj.Value'
      · simp only [Bool.false_eq_true, ↓reduceIte, _root_.false_and]
        exact upd_write ks g h x hlen hrv dzero zObj rfl
      · simp only [↓reduceIte]
        exact ⟨h, rfl⟩
  | some ki =>
    obtain ⟨hf, hr⟩ := krel_some h _ ki hk
    simp only [hf, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, updD]
    rw [preOk_rel x ki _ hr]
    cases hp : preOkL x (lookupL g.items x.Key').1.obj'
    · simp only [Bool.not_false, ↓reduceIte]
      exact ⟨h, rfl⟩
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hv : ki.obj.val = (lookupL g.items x.Key').1.obj'.Value' := congrArg (fun p => p.2.2) hr.1
    rw [hv]
    cases hrj : rejects x.Reject' (lookupL g.items x.Key').1.obj'.Value'
    · simp only [Bool.false_eq_true, ↓reduceIte, _root_.true_and]
      generalize hit : (lookupL g.items x.Key').1 = it at hr hv hp
      have heq : updObj x ki.obj = ki.obj ↔ sameObjL (updatedL x it.obj') it.obj' = true := by
        have key : updObj x ki.obj = ki.obj ↔ (updObj x ki.obj).1 = ki.obj.1 :=
          ⟨congrArg _, fun e => Subtype.ext e⟩
        rw [key, updObj_rel x hlen ki.obj it.obj' hr.1, hr.1]
        simp [sameObjL, and_assoc]
      by_cases hsame : sameObjL (updatedL x it.obj') it.obj' = true ∧ it.canon' = true
      · rw [if_pos ⟨heq.2 hsame.1, hr.2.2.trans hsame.2⟩, if_pos hsame]
        refine ⟨h, ?_⟩
        simp only [outOf]
        rw [itemRel_obj hr]
      · rw [if_neg (fun hc => hsame ⟨heq.1 hc.1, hr.2.2 ▸ hc.2⟩), if_neg hsame]
        exact upd_write ks g h x hlen hrv ki.obj it.obj' hr.1
    · simp only [↓reduceIte]
      exact ⟨h, rfl⟩

/-- **`Get`** of the input's name, with the minimum resource version `n` (the input's `MinRV`,
parsed) and `ignoreNotFound` as given. -/
theorem refine_get {E : Type} (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input) (n : w64)
    (hn : parseRVD x.MinRV' = some n) :
    outOf (ks.get (E := E) (mkeyL x.Key') (uint.nat n) x.IgnoreNotFound') = mgetL x g := by
  unfold KSt.get mgetL
  rw [hn]
  simp only [gt_iff_lt]
  have hrv : uint.nat g.rv = ks.rv := by rw [← h.2.1]; have := h.2.2.1; word
  by_cases hlt : ks.rv < uint.nat n
  · rw [if_pos hlt, if_pos (show uint.nat g.rv < uint.nat n by omega)]
    rfl
  rw [if_neg hlt, if_neg (show ¬ uint.nat g.rv < uint.nat n by omega)]
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

end k8s_etcd3
end EtcdGrove
end Perennial
