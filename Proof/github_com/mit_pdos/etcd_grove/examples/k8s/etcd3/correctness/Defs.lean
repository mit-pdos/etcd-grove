/-
Lean-first (no Rocq counterpart).

# Kubernetes' checker in the heap (k8s 7g step 3, `notes/k8s-7g-scope.md` §2.3 "The Go side")

The predicates the specs of `examples/k8s/etcd3/correctness` are written in, over the pure
functions of `RModel.lean`/`RReplay.lean`:

- `deepRO x d`: `k8sDeep.deepRep` read-only (`DFrac.discard`): the value `x` has the deep value
  `d` and every cell `DeepEqual` reads of it is frozen. The checker never writes an object once
  it is in a `Model`, a `Response` or a `Change` (each write is to a fresh copy, `DeepCopyObject`,
  before it is shared), so every such object is held read-only;
- `modelRep dq mp m`: the `*Model` `mp` holds `m : RM` (its items as read-only `*Obj`s at the
  store keys, its resource version, `CompactResourceVersion` 0, the prefix, the driver's
  `Versioner`, `NewFunc` and `NewListFunc`, and the D30g `NeedsRewrite` map), with fraction `dq`:
  `modelAt` (persistent, `DFrac.discard`: what `Step` and porcupine see; a `Model` is never
  written after `execute` returns it) and `modelOwn` (full: `Clone`'s result, which `create`,
  `update` and `delete` write); it carries the driver's package initialization, which the
  calls through its `NewFunc`, `Versioner` and objects need;
- `respRep r rr`: the `Response` value `r` has the view `rr : RResp`; `errRep` of its error
  (a deep value, storage's too-large error, or anything for `RErr.other`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.RReplay
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Base
public import Proof.k8s_io.apimachinery.pkg.api.errors.View
public import Spec.k8s_io.apimachinery.pkg.api.errors.SuggestsClientDelay

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section vals
variable [GooseExts] [GoSemanticsFunctions] [GoGlobalContext]

/-! ## The model -/

/-- The driver's `Versioner` (`versioner{}`), the Model's `Versioner`. -/
abbrev versionerV : k8s_io.apiserver.pkg.storage.Versioner :=
  interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner.ty
    #github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner.mk

/-- The driver's `newObj`, the Model's `NewFunc`. -/
abbrev newFuncV : GoFunc := functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj []

/-- The driver's `newObjList`, the Model's `NewListFunc`. -/
abbrev newListFuncV : GoFunc :=
  functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObjList []

/-- The `Model` struct of `m` with its two maps at `il` (`Items`) and `rl` (`NeedsRewrite`). -/
def modelVal (il rl : Loc) (m : RM) : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model :=
  ⟨il, m.rv, 0, m.pfx, versionerV, newFuncV, newListFuncV, rl⟩

end vals

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]

/-! ## Read-only deep values -/

/-- **`x` has the deep value `d`, read-only** (see the file header). -/
abbrev deepRO (x : GoInterface) (d : DeepV) : IProp GF := deepRep DFrac.discard x d

instance itemsRep_discard_persistent (sl : GoSlice) (o : Option (List Obj)) :
    Persistent (itemsRep (GF := GF) DFrac.discard sl o) := by
  cases o <;> unfold itemsRep <;> infer_instance

instance remRep_discard_persistent (rp : Loc) (o : Option w64) :
    Persistent (remRep (GF := GF) DFrac.discard rp o) := by
  cases o <;> unfold remRep <;> infer_instance

instance deepRO_persistent (x : GoInterface) (d : DeepV) :
    Persistent (deepRO (GF := GF) x d) := by
  induction d generalizing x with
  | nil => unfold deepRO deepRep; infer_instance
  | obj o => unfold deepRO deepRep; infer_instance
  | list items rv cont rem => unfold deepRO deepRep; infer_instance
  | storageErr code key rv inner ih =>
    unfold deepRO deepRep
    have : ∀ e, Persistent (deepRep (GF := GF) DFrac.discard e inner) := ih
    infer_instance
  | errString s => unfold deepRO deepRep; infer_instance

/-- A read-only `*Obj`. -/
theorem deepRO_obj (p : Loc) (o : Obj) :
    (p ↦□ o : IProp GF) ⊢ deepRO (interface.mkOk (go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p) (.obj o) := by
  iintro #H
  unfold deepRO deepRep
  iexists p
  iframe H
  ipureintro; rfl

/-- The items map's values: read-only `*Obj`s, key by key (`mapRep`, `reflect.DeepEqual`'s view of
the map, at the objects' deep values); and at most `2^62` of them (`slices.Sorted(maps.Keys(..))`'s
premise, `Spec.maps.Keys`). -/
def itemsRO (M : GMap GoString GoInterface) (items : GMap GoString Obj) : IProp GF :=
  iprop(⌜GMap.size items ≤ 2 ^ 62⌝ ∗ mapRep DFrac.discard M (GMap.fmap DeepV.obj items))

instance itemsRO_persistent (M : GMap GoString GoInterface) (items : GMap GoString Obj) :
    Persistent (itemsRO (GF := GF) M items) := by
  unfold itemsRO mapRep; infer_instance

/-- **The `*Model` `mp` holds `m`**, with fraction `dq` on the struct and the two maps (see the
file header). -/
def modelRep (dq : DFrac) (mp : Loc) (m : RM) : IProp GF :=
  iprop(isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
    ∃ (il rl : Loc) (M : GMap GoString GoInterface),
    mp ↦{dq} modelVal il rl m ∗ il ↦${dq} M ∗ itemsRO M m.items ∗ rl ↦${dq} m.rewrites)

/-- **A frozen `*Model`** (persistent). -/
abbrev modelAt (mp : Loc) (m : RM) : IProp GF := modelRep DFrac.discard mp m

/-- **An owned `*Model`.** -/
abbrev modelOwn (mp : Loc) (m : RM) : IProp GF := modelRep (DFrac.own 1) mp m

instance modelAt_persistent (mp : Loc) (m : RM) : Persistent (modelAt (GF := GF) mp m) := by
  unfold modelAt modelRep; infer_instance

/-- An owned model can be frozen. -/
theorem modelOwn_freeze (mp : Loc) (m : RM) : modelOwn (GF := GF) mp m ⊢ |==> modelAt mp m := by
  unfold modelAt modelOwn modelRep
  iintro ⟨#Hinit, %il, %rl, %M, Hm, HI, #Hit, HR⟩
  ipersist Hm
  imod ownMap_persist _ _ _ $$ HI with #HI
  imod ownMap_persist _ _ _ $$ HR with #HR
  imodintro
  iframe Hinit
  iexists il, rl, M
  iframe Hm HI Hit HR

/-! ## Responses -/

/-- **A `Response.Err` with the view `e`** (persistent): a deep value read-only; storage's
too-large error (`apierrors.tooLargeErrIs`), of code 504 (`IsTooManyRequests` answers `false`),
whose details, held read-only, give `delay` as `SuggestsClientDelay`'s answer (`apierrors.delayV`); for `other`, only that it is not `nil`
(`errNonNil`). -/
def errRep (x : GoInterface) : RErr → IProp GF
  | .deep d => deepRO x d
  | .tooLarge delay => iprop(apierrors.tooLargeErrIs x ∗
      ∃ (l : Loc) (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
        (dv : k8s_io.apimachinery.pkg.apis.«meta».v1.StatusDetails),
      ⌜x = interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l ∧
        st.Code' = W32 504 ∧ (apierrors.delayV st dv).2 = delay⌝ ∗
      l ↦□ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗ st.Details' ↦□ dv)
  | .other => iprop(⌜x ≠ GoInterface.nil⌝)

instance errRep_persistent (x : GoInterface) (e : RErr) : Persistent (errRep (GF := GF) x e) := by
  cases e <;> unfold errRep <;> infer_instance

/-- **`NewTooLargeResourceVersionError(_, _, 0)`'s error is `RErr.tooLarge false`** (its reason
`Timeout` and no retry: `SuggestsClientDelay` answers `false`). -/
theorem errRep_tooLarge_of (x : GoInterface) (l : Loc)
    (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
    (dv : k8s_io.apimachinery.pkg.apis.«meta».v1.StatusDetails)
    (h : x = interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l ∧
      st.Status' = go!"Failure" ∧ st.Reason' = go!"Timeout" ∧ st.Code' = W32 504 ∧
      dv.RetryAfterSeconds' = W32 (sint.Z (W64 0))) :
    (apierrors.tooLargeErrIs x ∗ l ↦□ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗
      st.Details' ↦□ dv : IProp GF) ⊢ errRep x (.tooLarge false) := by
  iintro ⟨#Ht, #Hl, #Hd⟩
  simp only [errRep]
  isplitr
  · iexact Ht
  iexists l, st, dv
  iframe Hl Hd
  ipureintro
  refine ⟨h.1, h.2.2.2.1, ?_⟩
  obtain ⟨-, -, hr, -, hd⟩ := h
  unfold apierrors.delayV
  rw [hr, hd]
  simp

/-- **The store's too-large error is `RErr.tooLarge false`** (`tooLargeErrIs` holds its code 504 and its
details with no retry: `SuggestsClientDelay` answers `false`; k8s 7g option (b1)). -/
theorem errRep_tooLarge_of_is (x : GoInterface) :
    apierrors.tooLargeErrIs (GF := GF) x ⊢ errRep x (.tooLarge false) := by
  iintro #Ht
  simp only [errRep]
  isplitr
  · iexact Ht
  iunfold apierrors.tooLargeErrIs at Ht
  icases Ht with ⟨%st, %cs, #Ha, %hst, %dv, #Hd, %hcr⟩
  iunfold apierrors.apiErrAt at Ha
  icases Ha with ⟨%l, %h, #Hl, -⟩
  iexists l, st, dv
  iframe Hl Hd
  ipureintro
  refine ⟨h, hcr.1, ?_⟩
  unfold apierrors.delayV
  rw [hst.1, hcr.2]
  simp

/-- **The `Response` `r` has the view `rr`** (persistent). -/
def respRep (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response)
    (rr : RResp) : IProp GF :=
  iprop(deepRO r.Object' rr.obj ∗ errRep r.Err' rr.err)

instance respRep_persistent (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response)
    (rr : RResp) : Persistent (respRep (GF := GF) r rr) := by
  unfold respRep; infer_instance

/-! ## Create's object -/

/-- **The object `realRequest(x)` asks to create** (resource version 0, no annotation): the one
`rcreateL` stores at the next resource version. -/
def createObjL (x : Input) : Obj :=
  ⟨(k8s_etcd3.splitKeyL x.Key').1, (k8s_etcd3.splitKeyL x.Key').2, x.UID', x.Val', x.Node', x.App',
    W64 0, false⟩

/-! ## Changes -/

/-- An optional object's deep value (`nil` for none). -/
def optObjD : Option Obj → DeepV
  | none => .nil
  | some o => .obj o

/-- **The `*Change` `cp` has the view `c`** (persistent): `nil` for none, else a frozen `Change`
with the key, the resource version and the objects' deep values read-only. -/
def changeRep (cp : Loc) : Option RChange → IProp GF
  | none => iprop(⌜cp = null⌝)
  | some c => iprop(∃ (ox opx : GoInterface),
      cp ↦□ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change.mk c.key c.rv ox opx ∗
      deepRO ox (optObjD c.obj) ∗ deepRO opx (optObjD c.prev))

instance changeRep_persistent (cp : Loc) (c : Option RChange) :
    Persistent (changeRep (GF := GF) cp c) := by
  cases c <;> unfold changeRep <;> infer_instance

/-! ## Object slices -/

/-- **The `[]runtime.Object` slice `sl` holds fresh copies of `os`** (owned, with its capacity):
each element a `*Obj` holding its object (`listItems`' result, `DeepCopyObject`s). -/
def objsOwn (sl : GoSlice) (os : List Obj) : IProp GF :=
  iprop(∃ xs : List GoInterface, sl ↦* xs ∗ ownSliceCap GoInterface sl (DFrac.own 1) ∗
    [∗list] x;o ∈ xs;os, deepRep (DFrac.own 1) x (.obj o))

/-! ## Read consistency -/

/-- A `ReadConsistency`'s string. -/
def rconsStr : RCons → GoString
  | .consistent => go!"Consistent"
  | .exact => go!"Exact"
  | .notOlderThan => go!"NotOlderThan"

/-! ## Nil-ness of a view -/

/-- An interface value with a deep view is nil iff its view is. -/
theorem deepRep_nil_iff (dq : DFrac) (x : GoInterface) (d : DeepV) :
    deepRep (GF := GF) dq x d ⊢ ⌜x = GoInterface.nil ↔ d = .nil⌝ := by
  cases d <;> unfold deepRep
  · iintro %h; ipureintro; simp [h]
  all_goals
    iintro H
    first
    | (icases H with ⟨%p, %h, -⟩; ipureintro; subst h; simp [interface.mkOk])
    | (icases H with ⟨%p, %sl, %rp, %h, -⟩; ipureintro; subst h; simp [interface.mkOk])
    | (icases H with ⟨%p, %e, %h, -⟩; ipureintro; subst h; simp [interface.mkOk])

/-- A `Response.Err` is nil iff its view says no error (`errNonNil`). -/
theorem errRep_nil_iff (x : GoInterface) (e : RErr) :
    errRep (GF := GF) x e ⊢ ⌜x = GoInterface.nil ↔ errNonNil e = false⌝ := by
  cases e with
  | deep d =>
    unfold errRep deepRO
    iintro H
    icases deepRep_nil_iff _ _ _ $$ H with %h
    ipureintro
    rw [h]
    cases d <;> simp [errNonNil]
  | tooLarge b =>
    unfold errRep
    iintro H
    unfold apierrors.tooLargeErrIs apierrors.apiErrAt
    icases H with ⟨⟨%st, %cs, ⟨%l, %h, -⟩, -⟩, -⟩
    ipureintro
    subst h
    simp [errNonNil, interface.mkOk]
  | other =>
    unfold errRep
    iintro %h
    ipureintro
    simp [errNonNil, h]

end defs

end k8s_correctness
end EtcdGrove
end Perennial
