/-
Lean-first (no Rocq counterpart).

# The checker's `Model` on the driver's objects (k8s 7g step 3)

- `itemsFitL m`: every item of the model fits the driver's objects (`fitsD`) and carries no
  annotation, so that it is an `objAtD` of its `DObj` (what `tryUpdateFor`'s closure and the
  driver's `metav1.Object` methods take); `rcreateL`, `rupdateL`, `rdeleteL` keep it
  (`itemsFitL_create`, ...), for an input that fits (`inFits`).
- `preMsgL_kpre`: the model's precondition message is `storage.Preconditions.Check`'s
  (`KPre.failMsg` of `kpreOf x`).
- `metaAt_obj`: a `*Obj` held at any fraction is a `metav1.Object` whose `GetUID` and
  `GetResourceVersion` answer its UID and `rvStr` of its resource version (what `Check` takes; the
  model checks a stored, read-only object).
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

/-- `Check`'s test is the model's (`preOkL`). -/
theorem kpreOf_ok (x : Input) (o : Obj) :
    (kpreOf x).ok o.UID' (rvStr o.ResourceVersion') = preOkL x o := by
  unfold kpreOf k8s.KPre.ok preOkL
  cases h1 : x.HasPreUID' <;> cases h3 : x.HasPreRV' <;> simp

set_option linter.unusedSimpArgs false in
/-- **The model's precondition message is `Check`'s.** -/
theorem preMsgL_kpre (x : Input) (o : Obj) (h : preOkL x o = false) :
    preMsgL x o = some ((kpreOf x).failMsg o.UID' (rvStr o.ResourceVersion')) := by
  unfold preMsgL k8s.KPre.failMsg kpreOf
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
