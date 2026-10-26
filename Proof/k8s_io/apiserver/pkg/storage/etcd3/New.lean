/-
Lean-first (no Rocq counterpart).

The proof of `New`: the path prefix (`path.Join("/", prefix)`, no trailing `/` to trim), the list
error aggregator (the default, or the corrupt-object one if the feature gate says so), the
watcher (its fields; the object type's name from `newFunc`'s object, `reflect`), the store (its
fields, read-only from here: what `isStore` reads), the lease manager, the metrics tracker; the
feature checker's `CheckClient` (the package's fact); the resource prefix's checks pass.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.newDefaultLeaseManager
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.defaultListErrorAggregatorFactory
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.corruptObjErrAggregatorFactory
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.newStorageKeyReverseFunc
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.NewEtcdMetricsTracker
public import Spec.path.Join
public import Proof.path.CleanAbs
public import Spec.strings.TrimSuffix
public import Spec.go_etcd_io.etcd.client.v3.Client__Ctx
public import Spec.reflect.TypeOf
public import Perennial.Proof.strings.HasPrefix
public import Proof.k8s_io.apiserver.pkg.features.Values

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem New.wp_proof
    (wp_lm : newDefaultLeaseManager.spec (GF := GF) (hG := hG))
    (wp_dla : defaultListErrorAggregatorFactory.spec (GF := GF) (hG := hG))
    (wp_cea : corruptObjErrAggregatorFactory.spec (GF := GF) (hG := hG))
    (wp_rk : newStorageKeyReverseFunc.spec (GF := GF) (hG := hG))
    (wp_mt : metrics.NewEtcdMetricsTracker.spec (GF := GF) (hG := hG))
    (wp_Join : path.Join.spec (GF := GF) (hG := hG))
    (wp_Trim : strings.TrimSuffix.spec (GF := GF) (hG := hG))
    (wp_Ctx : Client.Ctx.spec (GF := GF) (hG := hG))
    (wp_TypeOf : reflect.TypeOf.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ S kc cl ms V γh cmp codec nf nlf rkf pfx0 rp gr vi ti di lmc hp hrp hrp1
  wp_start as ⟨#Hkc, #Hnc, #Hwo, #Hregs, ⟨%cx, #Hcx⟩, #Hcon, #Hnf⟩
  ihave #Pft : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.util.feature $$ []
  · iPkgInit
  ihave #Hft : (k8s_io.apiserver.pkg.storage.etcd3.featureInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pft
  icases Hft with ⟨%g, #Hg, #Hen⟩
  ihave #Hkc' := Hkc
  iStructNamed Hkc'
  ihave #Psf : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.feature $$ []
  · iPkgInit
  ihave #Hck : (k8s_io.apiserver.pkg.storage.etcd3.checkerInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Psf
  ihave #Chk := Hck
  ihave #Psg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave #Hsg : (k8s_io.apiserver.pkg.storage.etcd3.storageInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Psg
  icases Hsg with ⟨%rw, %tl, #Hrw, -⟩
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %jsl ⟨Hjsl, -⟩
  ihave #Ppath : isPkgInit (PROP := IProp GF) pkg_id.path $$ []
  · iPkgInit
  wp_apply (path.Join_cleanAbs wp_Join _ _ pfx0 hp) $$ [Hjsl] as Hjsl
  · have heq : ([[47#8], zero_val GoString].set (sint.nat (W64 (0 + 1))) pfx0) =
        [go!"/", pfx0] := rfl
    rw [← heq]
    iexact Hjsl
  wp_apply wp_Trim
  have hnt : ¬ go!"/" <:+ pfx0 := hp.2.2.2.1
  simp only [hnt, ↓reduceIte]
  -- the resource prefix's checks pass
  have hne : rp ≠ [] := fun h => by rw [h] at hrp; simp at hrp
  rw [decide_eq_false hne]
  wp_auto
  rw [decide_eq_false hrp1]
  wp_auto
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_apply _root_.Perennial.strings.HasPrefix.wp_proof
  rw [decide_eq_true hrp]
  wp_auto
  -- the list error aggregator: the default, or (by the feature gate) the corrupt-object one
  have hnp : k8s_io.apiserver.pkg.features.AllowUnsafeMalformedObjectDeletion.isPanic = false :=
    features.AllowUnsafeMalformedObjectDeletion_notPanic
  wp_pure
  (try wp_auto)
  wp_apply Hen as %b
  cases b
  case' true =>
    (try wp_auto)
    wp_apply wp_cea as %fa -
  all_goals
    (try wp_auto)
    wp_apply wp_rk as %rkf' -
    (try wp_auto)
    -- the watcher's object type: `newFunc`'s object's type's name
    cases decide (nf = func.nil)
    case' false =>
      (try wp_auto)
      wp_apply Hnf as %x %Hx
      ihave #Pr : isPkgInit (PROP := IProp GF) pkg_id.reflect $$ []
      · iPkgInit
      (try wp_auto)
      wp_apply wp_TypeOf x $$ [] as %t #Ht
      · iframe #
        ipureintro; exact Hx
      wp_apply Ht as %s -
    all_goals
      (try wp_auto)
      wp_apply wp_lm as %lm -
      (try wp_auto)
      ihave #Pm : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
      · iPkgInit
      wp_apply wp_mt as %mt %lt ⟨#Hmt, %Hlt⟩
      (try wp_auto)
      rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
        (m := go!"Ctx")]
      wp_call
      (try wp_auto)
      wp_apply wp_Ctx cl cx $$ []
      · iframe #
      (try wp_auto)
      irename : («$r0_ptr» ↦ (_ : k8s_io.apiserver.pkg.storage.etcd3.store) : IProp GF) => Hsto
      icases (typedPointsto_not_null_dup _ _ _) $$ Hsto with ⟨Hst, %Hsn⟩
      ipersist Hst
      ihave #Hst' := Hst
      iStructNamed Hst'
      wp_apply Chk
      (try wp_auto)
      iapply HΦ
      isplitr
      · ipureintro; rfl
      iexists mt, lt
      iunfold isStore
      simp only
      iframe #
      ipureintro
      exact ⟨Hsn, Hlt⟩

end proof

end k8s
end EtcdGrove
end Perennial
