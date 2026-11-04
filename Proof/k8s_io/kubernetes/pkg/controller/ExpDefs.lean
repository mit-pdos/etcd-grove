/-
**The controller expectations' predicates** (`pkg/controller/controller_utils.go`'s
`ControllerExpectations`, a `cache.Store` of `*ControlleeExpectations` keyed by `ExpKeyFunc`;
phase 5 of `notes/k8s-daemonset-plan.md`). Lean-first.

The expectations do not matter for S1, so the counters are tracked loosely: only what makes every
operation return (no panic) is kept.

* `isCE e k` (persistent): `e` is a `*ControlleeExpectations` with key `k` (its `key` and
  `timestamp` fields read-only), its atomic counters `add`, `del` in an invariant (any values: a
  pointer may outlive its record in the store, and `Add` may run on it concurrently).
* `ceOK o`: the store's objects' contract (`cache`'s `OK`): `o` is a `*ControlleeExpectations`
  meeting `isCE`.
* `expKeyOk kf`: the key function's contract: on a `*ControlleeExpectations` it returns its key
  and no error (`ExpKeyFunc`'s closure, `expKeyFn`, meets it: `ExpKeyFunc.spec`).
* `isExp r γe` (persistent): `r` is a `*ControllerExpectations` whose `Store` is the `*cache`
  `γe.ca` (`isCache`), key function `γe.kf` meeting `expKeyOk`; the store's abstract state is in
  an invariant (`expInv`: no `nil` item), so that workers and event handlers share it.
* `expReader γe`: one of the store lock's reader slots (`tsReader`), which the readers
  (`GetExpectations`, `SatisfiedExpectations`, `DeleteExpectations`, `Lower`/`RaiseExpectations`,
  `Creation`/`DeletionObserved`) take and give back; `NewControllerExpectations` hands out all
  of them.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.k8s_io.client_go.tools.cache.CacheDefs
public import Spec.k8s_io.apimachinery.pkg.api.meta.Accessor_ControlleeExpectations

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI k8s_io.kubernetes.pkg.controller cache

/-- The expectations' names: the `*cache`, its thread-safe store and ghost names, its key
function. -/
structure ExpNames [GooseExts] where
  ca : Loc
  ts : Loc
  γ : TsNames
  kf : GoFunc

/-- The invariants' namespaces. -/
def expN : Namespace := nroot.@"dsctl_expectations"
def ceN : Namespace := nroot.@"dsctl_controllee"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [meta_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

/-- **A controllee's expectations** `e` with key `k` (persistent). -/
def isCE (e : Loc) (k : GoString) : IProp GF :=
  iprop(structFieldRef ControlleeExpectations go!"key" e ↦□ k ∗
    (∃ t : time.Time, structFieldRef ControlleeExpectations go!"timestamp" e ↦□ t) ∗
    inv ceN iprop(∃ a d : w64, structFieldRef ControlleeExpectations go!"add" e ↦ a ∗
      structFieldRef ControlleeExpectations go!"del" e ↦ d))

instance isCE_persistent (e : Loc) (k : GoString) : Persistent (isCE (GF := GF) e k) := by
  unfold isCE; infer_instance

/-- **The store's objects' contract**: `*ControlleeExpectations` meeting `isCE`. -/
def ceOK (o : GoInterface) : IProp GF :=
  iprop(∃ (e : Loc) (k : GoString),
    ⌜o = interface.mkOk (go.GoType.PointerType ControlleeExpectations.ty) #e⌝ ∗ isCE e k)

instance ceOK_persistent (o : GoInterface) : Persistent (ceOK (GF := GF) o) := by
  unfold ceOK; infer_instance

/-- The store's index functions' family: none is used (`NewStore` has no indexers). -/
def fam0 : Nat → Fn GF := fun _ _ _ => iprop(False)

/-- **The key function's contract**: a `*ControlleeExpectations`'s key, and no error. -/
def expKeyOk (kf : GoFunc) : IProp GF :=
  iprop(∀ (e : Loc) (k : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗
        structFieldRef ControlleeExpectations go!"key" e ↦□ k }}
      (App (Val #kf)
        (Val #(interface.mkOk (go.GoType.PointerType ControlleeExpectations.ty) #e : GoInterface)))
    {{ RET (PairV #k #(interface.nil : GoInterface)); True }})

instance expKeyOk_persistent (kf : GoFunc) : Persistent (expKeyOk (GF := GF) kf) := by
  unfold expKeyOk; infer_instance

instance storeSt_timeless (γ : TsNames) (σ : St) : Timeless (storeSt (GF := GF) γ σ) := by
  unfold storeSt; infer_instance

/-- The store holds no `nil` item. -/
def expNN (σ : St) : Prop := ∀ k o, σ.items !! k = some o → o ≠ interface.nil

/-- The store's state, shared: no `nil` item. -/
abbrev expInv (γe : ExpNames) : IProp GF :=
  iprop(∃ σ : St, storeSt γe.γ σ ∗ ⌜expNN σ⌝)

/-- **The expectations** `r` (persistent). -/
def isExp (r : Loc) (γe : ExpNames) : IProp GF :=
  iprop(structFieldRef ControllerExpectations go!"Store" r ↦□
      (interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #γe.ca :
        GoInterface) ∗
    isCache γe.ca γe.ts γe.γ ceOK fam0 γe.kf ∗ expKeyOk γe.kf ∗ inv expN (expInv γe))

instance isExp_persistent (r : Loc) (γe : ExpNames) : Persistent (isExp (GF := GF) r γe) := by
  unfold isExp; infer_instance

/-- **One of the expectations' reader slots.** -/
def expReader (γe : ExpNames) : IProp GF := tsReader γe.ts γe.γ ceOK fam0

theorem expNN_empty : expNN ⟨∅, [], ∅⟩ := by
  intro k o h; simp [GMap.lookup_empty] at h

theorem expNN_update (σ : St) (k : GoString) (o : GoInterface) (rvo : Option GoString)
    (h : expNN σ) (ho : o ≠ interface.nil) : expNN (σ.update k o rvo) := by
  intro k' o' h'
  simp only [St.update] at h'
  by_cases hk : k' = k
  · subst hk; simp only [GMap.lookup_insert, Option.some.injEq] at h'; subst h'; exact ho
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at h'; exact h k' o' h'

theorem expNN_delete (σ : St) (k : GoString) (rvo : Option GoString) (h : expNN σ) :
    expNN (σ.delete k rvo) := by
  intro k' o' h'
  simp only [St.delete] at h'
  by_cases hk : k' = k
  · subst hk; rw [GMap.lookup_delete] at h'; cases h'
  · rw [GMap.lookup_delete_ne _ (Ne.symm hk)] at h'; exact h k' o' h'

/-- The store call's object (the `D` of `cache.Add`/`Delete`): the `*ControlleeExpectations` `e`
with key `k`, and the packages the key function and `meta.Accessor` need. -/
def ceD (e : Loc) (k : GoString) (o : GoInterface) : IProp GF :=
  iprop(⌜o = interface.mkOk (go.GoType.PointerType ControlleeExpectations.ty) #e⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» ∗
    structFieldRef ControlleeExpectations go!"key" e ↦□ k)

instance ceD_persistent (e : Loc) (k : GoString) (o : GoInterface) :
    Persistent (ceD (GF := GF) e k o) := by
  unfold ceD; infer_instance

open Iris.ProofMode in
/-- The key function's contract on the call's object. -/
theorem ceD_keyOk (kf : GoFunc) (e : Loc) (k : GoString) :
    expKeyOk kf ⊢ keyOk (ceD (GF := GF) e k) kf (fun _ => k) := by
  iintro #Hkf
  unfold keyOk
  iintro %o !> %Φ #HD HΦ
  iunfold ceD at HD
  icases HD with ⟨%ho, #Hpkg, #Hmpkg, #Hk⟩
  subst ho
  unfold expKeyOk
  iapply Hkf $$ %e %k [] [HΦ]
  · iframe #
  inext
  iintro -
  iapply HΦ
  ipureintro; exact ⟨rfl, rfl⟩

open Iris.ProofMode in
/-- `meta.Accessor`'s contract on the call's object: no resource version. -/
theorem ceD_rvAcc (wp_Acc : apimeta.Accessor_ControlleeExpectations.spec (GF := GF) (hG := hG))
    (e : Loc) (k : GoString) :
    ⊢ rvAcc (ceD (GF := GF) e k) (fun _ => none) := by
  unfold rvAcc
  iintro %o !> %Φ #HD HΦ
  iunfold ceD at HD
  icases HD with ⟨%ho, #Hpkg, #Hmpkg, #Hk⟩
  subst ho
  iapply (wp_Acc e) $$ [] [HΦ]
  · iframe #
  inext
  iintro %m %err %Herr
  iapply HΦ
  ipureintro; exact Herr

open Iris.ProofMode in
/-- **A linearization point of the store**, through the invariant: the store's state `σ` (with
no `nil` item) becomes `f σ`, and the continuation `K σ` follows. -/
theorem exp_lin (γe : ExpNames) (f : St → St) (hf : ∀ σ, expNN σ → expNN (f σ))
    (K : St → IProp GF) :
    inv expN (expInv γe) ∗ (∀ σ, ⌜expNN σ⌝ -∗ K σ) ⊢
      |={⊤ \ ∅, ∅}=> ∃ σ, storeSt γe.γ σ ∗ (storeSt γe.γ (f σ) -∗ |={∅, ⊤ \ ∅}=> K σ) := by
  iintro ⟨#Hinv, HK⟩
  rw [Iris.Std.LawfulSet.diff_empty]
  iinv Hinv with Hi Hclose
  iunfold expInv at Hi
  imod Hi with ⟨%σ, Hst, %Hnn⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists σ
  iframe Hst
  iintro Hst
  imod Hmask
  imod Hclose $$ [Hst] with -
  · inext; iexists (f σ); iframe; ipureintro; exact hf σ Hnn
  imodintro
  iapply HK
  ipureintro; exact Hnn

end defs

section pkgfact
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The package's fact**: `ExpKeyFunc` holds `expKeyFn`, read-only for good. -/
theorem controller_expKeyFunc :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ⊢
      globalAddr ExpKeyFunc ↦□ expKeyFn := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller

end pkgfact

end dsctl
end EtcdGrove
end Perennial
