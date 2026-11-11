/-
Lean-first (no Rocq counterpart).

# The store's model refines the driver's (stage 6b of `notes/k8s-etcd3-plan.md`)

The store's specs answer in terms of `Model.lean`'s `KSt` (items by etcd key, resource versions
as numbers); the driver's model (`KModel.lean`'s `mstepL`) computes on `mstore`s (items sorted
by name, 64-bit resource versions). `KRel ks g` relates them: the same resource version, and at
every name `n`, the store's item at the etcd key `mkeyL n` (`"/registry/objs/" ++ n`) is `g`'s
item of `n` (7e-3c's `ItemRelH`: the whole object at the item's resource version, and the
canonical bit). `krelS_iff`: 7e-3c's `KRelS` of etcd's store is `KRel` of its abstraction.

`outOf r` is the driver's `Output` of the store's answer `r` (`call`: `objOut` of the object, an
`errOut` of the error; a callback's error is `ERejected`, a too-large resource version
`ETooLarge`). For each operation, on related states, the store's model and the driver's answer the
same and stay related (`refine_create`, `refine_delete`, `refine_update`, `refine_get`), given the
next resource version fits 64 bits and the input's fields fit an object (`crFits`, `inFits`).
Stage 7b: the input's preconditions (`kpreOf`, the store's `preOk`), updates with
`ignoreNotFound` (from `dzero`), and a `Get`'s minimum resource version. Stage 7e-4: the objects'
namespace, node and app (`mkObj`, `crObjL`), the callbacks' rejection on the node, `ETooLarge`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RefineList

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

/-- **The store's state and the driver's** (see the file header): the driver's items sorted, the
same resource version (below `2^64`), and at every name the same item (`PairRelH`: the whole
object at the item's resource version, and the canonical bit; stage 7e-4 on 7e-3c's relation). -/
def KRel (ks : KSt DObj) (g : GSt) : Prop :=
  SortedI g.items ∧ W64 (ks.rv : Int) = g.rv ∧ ks.rv < 2 ^ 64 ∧
    ∀ n, PairRelH (ks.items (mkeyL n)) (lookupL g.items n)

/-- **`KRelS` is `KRel` of the store's abstraction** (`absK` under the store's prefix). -/
theorem krelS_iff (s : KVStore) (rv : Nat) (g : GSt) (hrv : rv < 2 ^ 64) :
    KRelS s rv g ↔ KRel (absK driverCodec.dec kpfxD ⟨linkv.absM s.kvs, rv⟩) g := by
  unfold KRelS KRel
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, hrv, c⟩, fun ⟨a, b, _, c⟩ => ⟨a, b, c⟩⟩

/-- **The driver's output of a store answer** (`call`'s `objOut`/`errOut`). -/
def outOf {E : Type} : KResp DObj E → Output
  | .obj o rv => objOutL (o.toObj (W64 (rv : Int)))
  | .zero => zeroOutL
  | .err (.notFound k rv) => errOutL (W64 1) k (W64 (rv : Int))
  | .err (.keyExists k) => errOutL (W64 2) k (W64 0)
  | .err (.invalidObj k) => errOutL (W64 5) k 0
  | .err (.tooLarge _ _) => tooLargeL
  | .err (.user _) => rejectedL
  | .err _ => otherL

/-- **The store's preconditions of an input** (`preconditions(in)`, stage 7b): the UID and the
resource version's string, where given. -/
def kpreOf (x : Input) : KPre :=
  ⟨if x.HasPreUID' then some x.PreUID' else none, if x.HasPreRV' then some x.PreRV' else none⟩

/-- `call`'s object for a `Create` of `x`, as Go builds it (`&Obj{Namespace: ns, Name: name, UID:
in.UID, Value: in.Val, Node: in.Node, App: in.App}`, `splitKey(in.Key)`), at the resource version
`n`. -/
def crObjL (x : Input) (n : w64) : Obj :=
  ⟨(splitKeyL x.Key').1, (splitKeyL x.Key').2, x.UID', x.Val', x.Node', x.App', n, false⟩

/-- The input's fields a `Create` writes fit a `DObj` (they are drawn short, `GenIn`). -/
def crFits (x : Input) : Prop :=
  x.Key'.length < 256 ∧ x.UID'.length < 256 ∧ x.Node'.length < 256 ∧ x.App'.length < 256

theorem crFits_fitsD (x : Input) (h : crFits x) (n : w64) : fitsD (crObjL x n) := by
  obtain ⟨hk, hu, hn, ha⟩ := h
  have hc := splitKeyL_length x.Key'
  exact ⟨by simp only [crObjL]; omega, by simp only [crObjL]; omega, hu, hn, ha⟩

/-- **`call`'s object for a `Create`**, as the store's: `crObjL`'s (the zero object if it does not
fit: never, `crFits`). -/
def mkObj (x : Input) : DObj :=
  if h : fitsD (crObjL x 0) then DObj.ofObj _ h else dzero

theorem mkObj_toObj (x : Input) (h : crFits x) (n : w64) : (mkObj x).toObj n = crObjL x n := by
  unfold mkObj
  rw [dif_pos (crFits_fitsD x h 0)]
  rfl

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
  cases b <;> simp [PairRelH]

/-- The related states at the name `n`: both present. -/
theorem krel_some {ks : KSt DObj} {g : GSt} (h : KRel ks g) (n : GoString) (ki : KItem DObj)
    (hn : ks.items (mkeyL n) = some ki) :
    (lookupL g.items n).2 = true ∧ ItemRelH ki (lookupL g.items n).1 := by
  have := h.2.2.2 n
  rw [hn] at this
  revert this
  rcases lookupL g.items n with ⟨it, b⟩
  cases b <;> simp [PairRelH]

/-- A write at `key` keeps the relation elsewhere and relates the new item. -/
theorem krel_set (ks : KSt DObj) (g : GSt) (h : KRel ks g) (key : GoString) (ki : KItem DObj)
    (it : item) (hk : it.key' = key) (hr : ItemRelH ki it) (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel ⟨ks.setItem (mkeyL key) ki, ks.rv + 1⟩ ⟨setItemL g.items it, g.rv + W64 1⟩ := by
  obtain ⟨hs, hrv0, -, hall⟩ := h
  refine ⟨sortedI_setItemL _ _ hs, ?_, hrv, ?_⟩
  · show W64 ((ks.rv + 1 : Nat) : Int) = g.rv + W64 1
    rw [w64_succ _ hrv, hrv0]
  · intro n
    simp only [KSt.setItem]
    rw [lookupL_setItemL _ _ hs]
    by_cases hn : n = key
    · subst hn; simp [hk, PairRelH, hr]
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
    · subst hn; simp [PairRelH]
    · have h1 : mkeyL n ≠ mkeyL key := fun he => hn (mkeyL_inj he).symm
      rw [if_neg h1, if_neg hn]
      exact hall n

/-! ## The operations -/

/-- **`Create`** of `call`'s object (`mkObj`: the key's namespace and name, the input's UID, value,
node and app; no resource version). -/
theorem refine_create {E : Type} (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input)
    (hf : crFits x) (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (ks.create (E := E) (mkeyL x.Key') (mkObj x) 0).1 (mcreateL x g).1 ∧
      outOf (ks.create (E := E) (mkeyL x.Key') (mkObj x) 0).2 = (mcreateL x g).2 := by
  unfold KSt.create mcreateL
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  have hw : W64 ((ks.rv + 1 : Nat) : Int) = g.rv + W64 1 := by rw [w64_succ _ hrv, h.2.1]
  cases hk : ks.items (mkeyL x.Key') with
  | some ki =>
    have := (krel_some h _ ki hk).1
    simp only [this, ↓reduceIte]
    exact ⟨h, rfl⟩
  | none =>
    have hn := krel_none h _ hk
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    refine ⟨krel_set ks g h x.Key' _ _ rfl ⟨?_, rfl⟩ hrv, ?_⟩
    · rw [hw, mkObj_toObj x hf]; rfl
    · simp only [outOf]
      rw [hw, mkObj_toObj x hf]; rfl

/-- **The store's preconditions are the driver's** (`preOk`) on related objects. -/
theorem preOk_rel (x : Input) (ki : KItem DObj) (it : item) (h : ItemRelH ki it) :
    driverCodec.preOk (kpreOf x) ki.obj ki.rv = preOkL x it.obj' := by
  rw [h.1]
  simp only [ObjCodec.preOk, driverCodec, KPre.ok, kpreOf, preOkL]
  cases x.HasPreUID' <;> cases x.HasPreRV' <;> simp <;> congr

/-- Two objects at any resource versions are the same (`sameObj`) iff they are equal. -/
theorem sameObjL_toObj (a b : DObj) (m n : w64) :
    sameObjL (a.toObj m) (b.toObj n) = true ↔ a = b := by
  rw [DObj.ext_iff']
  simp [sameObjL, DObj.toObj, and_assoc]

/-- `updObj`'s record at another resource version. -/
theorem updObj_with (x : Input) (hi : inFits x) (o : DObj) (m n : w64) :
    { updGo x (o.toObj m) with ResourceVersion' := n } = (updObj x o).toObj n := by
  rw [updObj_toObj x o n hi, updGo_toObj x o m, updGo_toObj x o n]

/-- **`Delete`** of the input's name, with the input's preconditions (`kpreOf`) and
`validateFor(in.HasReject, in.Reject)` rejecting with `eD`. -/
theorem refine_delete (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input) (eD : GoInterface)
    (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (ks.delete (mkeyL x.Key') (driverCodec.preOk (kpreOf x))
        (rejD eD x.HasReject' x.Reject')).1 (mdeleteL x g).1 ∧
      outOf (ks.delete (mkeyL x.Key') (driverCodec.preOk (kpreOf x))
        (rejD eD x.HasReject' x.Reject')).2 = (mdeleteL x g).2 := by
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
    have hnode : ki.obj.node = (lookupL g.items x.Key').1.obj'.Node' := by rw [hr.1]
    rw [hnode]
    cases hrj : rejects x.HasReject' x.Reject' (lookupL g.items x.Key').1.obj'.Node'
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨krel_del ks g h x.Key' hrv, ?_⟩
      simp only [outOf]
      rw [hr.1, w64_succ _ hrv, h.2.1]
    · simp only [↓reduceIte]
      exact ⟨h, rfl⟩

/-- An update's write: the relation kept, the answers alike. -/
theorem upd_write {E : Type} (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input)
    (hi : inFits x) (hrv : ks.rv + 1 < 2 ^ 64) (o : DObj) (m : w64) :
    KRel ⟨ks.setItem (mkeyL x.Key') ⟨updObj x o, ks.rv + 1, true⟩, ks.rv + 1⟩
        ⟨setItemL g.items ⟨x.Key', { updGo x (o.toObj m) with ResourceVersion' := g.rv + W64 1 },
          true⟩, g.rv + W64 1⟩ ∧
      outOf (E := E) (.obj (updObj x o) (ks.rv + 1)) =
        objOutL { updGo x (o.toObj m) with ResourceVersion' := g.rv + W64 1 } := by
  have hw : W64 ((ks.rv + 1 : Nat) : Int) = g.rv + W64 1 := by rw [w64_succ _ hrv, h.2.1]
  rw [updObj_with x hi o m]
  refine ⟨krel_set ks g h x.Key' _ _ rfl ⟨by rw [hw], rfl⟩ hrv, ?_⟩
  simp only [outOf, hw]

/-- **`GuaranteedUpdate`** of the input's name by `tryUpdateFor(in)` (rejecting with `eU`), with
the input's preconditions (`kpreOf`) and `ignoreNotFound` (from the zero object `dzero`, which
`updated` names after the key). -/
theorem refine_update (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input) (eU : GoInterface)
    (hi : inFits x) (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (ks.update (mkeyL x.Key') x.IgnoreNotFound' dzero (driverCodec.preOk (kpreOf x))
        (updD eU x)).1 (mupdateL x g).1 ∧
      outOf (ks.update (mkeyL x.Key') x.IgnoreNotFound' dzero (driverCodec.preOk (kpreOf x))
        (updD eU x)).2 = (mupdateL x g).2 := by
  unfold KSt.update KSt.current mupdateL
  cases hk : ks.items (mkeyL x.Key') with
  | none =>
    have hn := krel_none h _ hk
    cases hig : x.IgnoreNotFound'
    · simp only [hn, hig, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
      refine ⟨h, ?_⟩
      simp only [outOf, notFoundL, h.2.1]
    · simp only [hn, hig, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]
      have hpz : driverCodec.preOk (kpreOf x) dzero 0 = preOkL x zObj :=
        preOk_rel x ⟨dzero, 0, true⟩ ⟨x.Key', zObj, true⟩ ⟨rfl, rfl⟩
      rw [hpz]
      cases hp : preOkL x zObj
      · simp only [Bool.not_false, ↓reduceIte]
        exact ⟨h, rfl⟩
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, updD]
      rw [show dzero.node = zObj.Node' from rfl]
      cases hrj : rejects x.HasReject' x.Reject' zObj.Node'
      · simp only [Bool.false_eq_true, ↓reduceIte, _root_.false_and]
        exact upd_write ks g h x hi hrv dzero (W64 0)
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
    have hnode : ki.obj.node = (lookupL g.items x.Key').1.obj'.Node' := by rw [hr.1]
    rw [hnode]
    cases hrj : rejects x.HasReject' x.Reject' (lookupL g.items x.Key').1.obj'.Node'
    · simp only [Bool.false_eq_true, ↓reduceIte, _root_.true_and]
      generalize hit : (lookupL g.items x.Key').1 = it at hr hnode hp
      obtain ⟨hro, hrc⟩ := hr
      rw [hro]
      have heq : updObj x ki.obj = ki.obj ↔
          sameObjL (updGo x (ki.obj.toObj (W64 (ki.rv : Int)))) (ki.obj.toObj (W64 (ki.rv : Int)))
            = true := by
        rw [← updObj_toObj x ki.obj _ hi, sameObjL_toObj]
      by_cases hsame : sameObjL (updGo x (ki.obj.toObj (W64 (ki.rv : Int))))
          (ki.obj.toObj (W64 (ki.rv : Int))) = true ∧ it.canon' = true
      · rw [if_pos ⟨heq.2 hsame.1, hrc.trans hsame.2⟩, if_pos hsame]
        exact ⟨h, rfl⟩
      · rw [if_neg (fun hc => hsame ⟨heq.1 hc.1, hrc ▸ hc.2⟩), if_neg hsame]
        exact upd_write ks g h x hi hrv ki.obj _
    · simp only [↓reduceIte]
      exact ⟨h, rfl⟩

/-- **`Get`** of the input's name, with the minimum resource version `n` (the input's `MinRV`,
parsed) and `ignoreNotFound` as given: `ETooLarge` above the store's resource version. -/
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
    rw [hr.1]

end go

end k8s_etcd3
end EtcdGrove
end Perennial
