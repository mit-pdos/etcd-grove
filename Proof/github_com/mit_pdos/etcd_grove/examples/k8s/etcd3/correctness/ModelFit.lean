/-
Lean-first (no Rocq counterpart).

# The checker's `Model` on the driver's objects (k8s 7g step 3)

- `itemsFitL m`: every item of the model fits the driver's objects (`fitsD`) and carries no
  annotation, so that it is an `objAtD` of its `DObj` (what `tryUpdateFor`'s closure and the
  driver's `metav1.Object` methods take); `rcreateL`, `rupdateL`, `rdeleteL` keep it
  (`itemsFitL_create`, ..., `itemsFitL_exec`), for an input that fits (`crFits`).
- `checkMsgL_kpre`: the model's precondition message is `storage.Preconditions.Check`'s
  (`KPre.failMsg` of `kpreOf x`).
- `metaAt_obj`: a `*Obj` held at any fraction is a `metav1.Object` whose `GetUID` and
  `GetResourceVersion` answer its UID and `rvStr` of its resource version (what `Check` takes; the
  model checks a stored, read-only object).
- `reqRep r x`: the `Request` `r` is `realRequest(x)` (`realcheck.go`), as `execute` reads it.
- `errVar_deep`: a driver error variable's value (`errVarOk`) has the deep value of its message
  (`updRejE`, `delRejE`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Callbacks
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Refine
public import Proof.k8s_io.apiserver.pkg.storage.InvalidMsg
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__GetUID
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__GetResourceVersion

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

variable [GooseExts]

/-- **The model's items are the driver's objects**: each fits a `DObj` and is not annotated. -/
def itemsFitL (m : RM) : Prop :=
  ∀ k o, m.items !! k = some o → fitsD o ∧ o.Annotated' = false

/-- `updGo` keeps an object that fits fitting, for an input that fits, and its annotation. -/
theorem updGo_fitsD (x : Input) (v : Obj) (hv : fitsD v) (hx : inFits x) : fitsD (updGo x v) := by
  obtain ⟨hk, hn, ha⟩ := hx
  obtain ⟨f1, f2, f3, f4, f5⟩ := hv
  have hc := splitKeyL_length x.Key'
  unfold updGo
  split
  · exact ⟨f1, f2, f3, f4, f5⟩
  · refine ⟨?_, ?_, f3, hn, ha⟩ <;> dsimp only <;> split <;> omega

theorem updGo_annotated (x : Input) (v : Obj) : (updGo x v).Annotated' = v.Annotated' := by
  unfold updGo; split <;> rfl

/-- **`create` keeps `itemsFitL`**, for an input whose fields fit (`crFits`). -/
theorem itemsFitL_create (x : Input) (m : RM) (hm : itemsFitL m) (hx : crFits x) :
    itemsFitL (rcreateL x m).2.1 := by
  unfold rcreateL failR
  dsimp only
  split
  · exact hm
  split
  · exact hm
  intro k o h
  simp only [GMap.lookup_insert_eq_iff] at h
  split at h
  · cases h; exact ⟨crFits_fitsD x hx (m.rv + W64 1), rfl⟩
  · exact hm k o h

/-- **`update` keeps `itemsFitL`**, for an input that fits (`inFits`). -/
theorem itemsFitL_update (x : Input) (m : RM) (hm : itemsFitL m) (hx : inFits x) :
    itemsFitL (rupdateL x m).2.1 := by
  have hcur : fitsD ((m.items !! storeKeyL x.Key').getD zObj) ∧
      ((m.items !! storeKeyL x.Key').getD zObj).Annotated' = false := by
    cases hs : m.items !! storeKeyL x.Key' with
    | none => exact ⟨by unfold fitsD zObj; simp, rfl⟩
    | some s => exact hm _ _ hs
  have hw : ∀ st, itemsFitL (updWriteL m (storeKeyL x.Key') st
      (updGo x ((m.items !! storeKeyL x.Key').getD zObj))).2.1 := by
    intro st k o h
    unfold updWriteL at h
    simp only [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h
      have hf := updGo_fitsD x _ hcur.1 hx
      refine ⟨⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩, ?_⟩
      exact (updGo_annotated x _).trans hcur.2
    · exact hm k o h
  unfold rupdateL failR
  dsimp only
  split
  · exact hm
  split
  · exact hm
  split
  · exact hm
  split
  · exact hm
  split
  · split
    · exact hm
    · exact hw _
  · exact hw _

/-- **`delete` keeps `itemsFitL`.** -/
theorem itemsFitL_delete (x : Input) (m : RM) (hm : itemsFitL m) :
    itemsFitL (rdeleteL x m).2.1 := by
  unfold rdeleteL failR
  dsimp only
  split
  · exact hm
  split
  · exact hm
  split
  · exact hm
  split
  · exact hm
  intro k o h
  simp only [GMap.lookup_delete_iff] at h
  split at h
  · cases h
  · exact hm k o h

/-- **Every model step keeps `itemsFitL`** (`execute`'s next state), for an input whose fields fit. -/
theorem itemsFitL_exec (x : Input) (m : RM) (hm : itemsFitL m) (hx : crFits x) :
    itemsFitL (rexecL x m).2.1 := by
  have hi : inFits x := ⟨hx.1, hx.2.2.1, hx.2.2.2⟩
  unfold rexecL
  split
  · exact hm
  split
  · exact itemsFitL_create x m hm hx
  split
  · exact itemsFitL_delete x m hm
  split
  · exact itemsFitL_update x m hm hi
  · exact hm

/-- `Check`'s test is the model's (`preOkL`). -/
theorem kpreOf_ok (x : Input) (o : Obj) :
    (kpreOf x).ok o.UID' (rvStr o.ResourceVersion') = preOkL x o := by
  unfold kpreOf k8s.KPre.ok preOkL
  cases h1 : x.HasPreUID' <;> cases h3 : x.HasPreRV' <;> simp

set_option linter.unusedSimpArgs false in
/-- **The model's precondition message is `Check`'s.** -/
theorem checkMsgL_kpre (x : Input) (o : Obj) (h : preOkL x o = false) :
    checkMsgL x o = some ((kpreOf x).failMsg o.UID' (rvStr o.ResourceVersion')) := by
  unfold checkMsgL k8s.KPre.failMsg kpreOf
  unfold preOkL at h
  cases h1 : x.HasPreUID' <;> cases h3 : x.HasPreRV' <;>
    by_cases h2 : x.PreUID' = o.UID' <;> by_cases h4 : x.PreRV' = rvStr o.ResourceVersion' <;>
    simp only [h1, h2, h3, h4, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
      decide_true, decide_false, Bool.not_true, Bool.not_false, Option.all_some, Option.all_none,
      Option.getD_some, ite_true, ite_false, Bool.false_eq_true,
      ↓reduceIte] at h ⊢ <;> trivial

section metaobj
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
variable [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- **A `*Obj` is a `metav1.Object`** at any fraction (`Check`'s `metaAt`). -/
theorem metaAt_obj (wp_UID : k8s_etcd3.Obj.GetUID.spec (GF := GF) (hG := hG))
    (wp_RV : k8s_etcd3.Obj.GetResourceVersion.spec (GF := GF) (hG := hG))
    (hty : objTyOk) (p : Loc) (dq : DFrac) (v : Obj) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ⊢
    k8s.metaAt (interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p)
      (p ↦{dq} v) v.UID' (rvStr v.ResourceVersion') := by
  iintro #Hpkg
  unfold k8s.metaAt
  isplitr
  · imodintro
    iintro -
    ipureintro
    exact ⟨_, rfl, hty.2.2⟩
  isplitr
  · imodintro
    iintro %ii %Φ %hx Hp HΦ
    cases hx
    wp_apply wp_UID $$ [$Hp] as Hp
    iapply HΦ
    iexact Hp
  · imodintro
    iintro %ii %Φ %hx Hp HΦ
    cases hx
    wp_apply wp_RV $$ [$Hp] as Hp
    iapply HΦ
    iexact Hp

/-- **A driver object is a `metav1.Object`** (as `driver_metaOk`, `Contract.lean`): `Check`'s
`metaAt` of an `objAtD`. -/
theorem metaAt_objAtD (wp_UID : k8s_etcd3.Obj.GetUID.spec (GF := GF) (hG := hG))
    (wp_RV : k8s_etcd3.Obj.GetResourceVersion.spec (GF := GF) (hG := hG))
    (hty : objTyOk) (x : GoInterface) (o : DObj) (rv : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ⊢
    k8s.metaAt x (objAtD x o rv) o.uid rv := by
  iintro #Hpkg
  unfold k8s.metaAt
  isplitr
  · imodintro
    iintro Hx
    iunfold objAtD at Hx
    icases Hx with ⟨%p, %n, %h, -⟩
    obtain ⟨rfl, -, -⟩ := h
    ipureintro
    exact ⟨_, rfl, hty.2.2⟩
  isplitr
  · imodintro
    iintro %ii %Φ %hx Hx HΦ
    iunfold objAtD at Hx
    icases Hx with ⟨%p, %n, %h, Hp⟩
    obtain ⟨rfl, hpn, hrv⟩ := h
    cases hx
    wp_apply wp_UID $$ [$Hp] as Hp
    iapply HΦ
    iunfold objAtD
    iexists p, n
    iframe Hp
    ipureintro; exact ⟨rfl, hpn, hrv⟩
  · imodintro
    iintro %ii %Φ %hx Hx HΦ
    iunfold objAtD at Hx
    icases Hx with ⟨%p, %n, %h, Hp⟩
    obtain ⟨rfl, hpn, rfl⟩ := h
    cases hx
    wp_apply wp_RV $$ [$Hp] as Hp
    iapply HΦ
    iunfold objAtD
    iexists p, n
    iframe Hp
    ipureintro; exact ⟨rfl, hpn, rfl⟩

/-- An item that fits, as an `objAtD` at its resource version (`p ↦ o` is its object's). -/
theorem objAtD_of_fit (p : Loc) (o : Obj) (hf : fitsD o) (ha : o.Annotated' = false) :
    (p ↦ o : IProp GF) ⊢ objAtD (interface.mkOk (go.GoType.PointerType objTyD) #p)
      (DObj.ofObj o hf) (rvStr o.ResourceVersion') := by
  iintro Hp
  icases (typedPointsto_not_null_dup _ _ _) $$ Hp with ⟨Hp, %Hn⟩
  iunfold objAtD
  iexists p, o.ResourceVersion'
  isplitr
  · ipureintro; exact ⟨rfl, Hn, rfl⟩
  rw [DObj.ofObj_toObj_rv o hf ha]
  iexact Hp

/-- **The request `r` is `realRequest(x)`** (persistent; `realcheck.go`): a list of `x.ListKey`
with `listOptions(x)`; a create at `x`'s store key of a read-only `*Obj` holding `createObjL x`; a
delete or an update at it with `preconditions(x)` and the closures `validateFor`/`tryUpdateFor`
make (not the nil func; the update's `IgnoreNotFound`); else a get with `MinRV` and
`IgnoreNotFound`. -/
def reqRep (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request)
    (x : Input) : IProp GF :=
  if x.Kind' = W64 4 then
    iprop(⌜r.Op' = go!"List" ∧ r.Key' = x.ListKey' ∧ r.List'.Options' = listOptsV x⌝)
  else if x.Kind' = W64 0 then
    iprop(⌜r.Op' = go!"Create" ∧ r.Key' = storeKeyL x.Key'⌝ ∗ ∃ op : Loc,
      ⌜r.Create'.Object' = interface.mkOk
        (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #op⌝ ∗
      op ↦□ createObjL x)
  else if x.Kind' = W64 1 then
    iprop(⌜r.Op' = go!"Delete" ∧ r.Key' = storeKeyL x.Key' ∧
        r.Delete'.ValidateDeletion' ≠ func.nil⌝ ∗
      k8s.preAt r.Delete'.Preconditions' (kpreOf x) ∗
      validateD x.HasReject' x.Reject' r.Delete'.ValidateDeletion')
  else if x.Kind' = W64 2 then
    iprop(⌜r.Op' = go!"Update" ∧ r.Key' = storeKeyL x.Key' ∧
        r.Update'.IgnoreNotFound' = x.IgnoreNotFound' ∧ r.Update'.UpdateFunc' ≠ func.nil⌝ ∗
      k8s.preAt r.Update'.Preconditions' (kpreOf x) ∗ tryUpdateD x r.Update'.UpdateFunc')
  else
    iprop(⌜r.Op' = go!"Get" ∧ r.Key' = storeKeyL x.Key' ∧
      r.Get'.Options'.ResourceVersion' = x.MinRV' ∧
      r.Get'.Options'.IgnoreNotFound' = x.IgnoreNotFound'⌝)

instance reqRep_persistent (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request)
    (x : Input) : Persistent (reqRep (GF := GF) r x) := by
  unfold reqRep; repeat (first | infer_instance | split)

/-- **A driver error variable's value has its message's deep value.** -/
theorem errVar_deep (X msg : GoString) (err : GoInterface) :
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errVarOk X msg ∗ globalAddr X ↦□ err :
      IProp GF) ⊢ deepRO err (.errString msg) := by
  iintro ⟨⟨%l, #Hg, -, #Hs⟩, #He⟩
  icombine Hg He gives %Heq
  unfold deepRO deepRep
  iexists l
  iframe Hs
  ipureintro
  exact Heq.symm

end metaobj

end k8s_correctness
end EtcdGrove
end Perennial
