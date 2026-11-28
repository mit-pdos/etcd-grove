/-
Lean-first (no Rocq counterpart). The driver's side of the store's watch path (stage E of k8s
7f-6, plan §3 step 7(v)), from the specs of the functions it calls:

- `watchContractOk_driver`: the watch path's object contract `watchContractOk driverSpec driverW
  codecI`: `runtime.Decode(codec{}, data)` is the codec's `Decode(data, nil, nil)` (a fresh `*Obj` of
  the data's object at resource version `0`, or an error), and
  `storage.AnnotateInitialEventsEndBookmark` of a driver object goes through its `GetAnnotations`
  (`nil`: the store's objects are not annotated) and `SetAnnotations` (the key set to `"true"`), so
  the object is `driverW`'s annotated one;
- `newItemOk_driver`: `newObj` is the store's `newFunc` for the driver (`newObj`'s zero object);
- `storeCfgD`: the configuration `newStore` makes the store with (the driver's object spec, codec,
  versioner, transformer and decoder, `/registry` and `/objs`, over the kubernetes client `kc`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WRun
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Contract
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec__Decode
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__GetAnnotations
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__SetAnnotations
public import Spec.k8s_io.apimachinery.pkg.runtime.Decode
public import Spec.k8s_io.apiserver.pkg.storage.AnnotateInitialEventsEndBookmark
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.EtcdClientInProc

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s

section cfg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- **The driver's store configuration** (see the file header): over the kubernetes client `kc`
(its etcd client `cl`, the in-process client of the members `ms` with the watch environment `V`,
`inProcEtcd ms V`), the metrics trackers
`mt lt` (`New`'s), the history names `γh`. -/
def storeCfgD [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] (kc cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (mt lt : Loc)
    (γh : GName) : k8s.StoreCfg GF DObj :=
  { S := driverSpec, codec := codecI, vi := versionerI, ti := identityI, di := decoderI,
    pathPrefix := go!"/registry", resourcePrefix := go!"/objs", gr := ⟨[], go!"objs"⟩, kc := kc,
    cl := cl, K := inProcEtcd ms V, mt := mt, lt := lt, γh := γh }

end cfg

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- **`newObj` is the driver's `newFunc`** (see the file header). -/
theorem newItemOk_driver (wp_newObj : newObj.spec (GF := GF) (hG := hG)) :
    ⊢ newItemOk (driverSpec (GF := GF))
      (functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj []) := by
  unfold newItemOk
  rw [show (driverSpec (GF := GF)).objAt = objAtD from rfl,
    show (driverSpec (GF := GF)).zero = dzero from rfl]
  imodintro
  iintro %Φ HΦ
  wp_apply wp_newObj as %x Hx
  iapply HΦ
  iexact Hx

/-- **The driver's watch contract** (see the file header). -/
theorem watchContractOk_driver
    (wp_Decode : runtime.Decode.spec (GF := GF) (hG := hG))
    (wp_cDecode : codec.Decode.spec (GF := GF) (hG := hG))
    (wp_Annotate : storage.AnnotateInitialEventsEndBookmark.spec (GF := GF) (hG := hG))
    (wp_GetAnn : Obj.GetAnnotations.spec (GF := GF) (hG := hG))
    (wp_SetAnn : Obj.SetAnnotations.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ⊢
      watchContractOk (driverSpec (GF := GF)) driverW codecI := by
  iintro #Hpkg
  ihave #Pr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime $$ []
  · iPkgInit
  ihave #Ps : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  unfold watchContractOk
  isplitr
  · imodintro
    iintro %dsl %d %Φ #Hd HΦ
    have e : codecI = GoInterface.ok
        ⟨github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec.ty,
          #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec.mk)⟩ := rfl
    rw [e]
    wp_apply (wp_Decode _ dsl (isPkgInit (PROP := IProp GF)
        pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3)
      (fun x err => match (driverSpec (GF := GF)).decode d with
        | some o => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ rv, (driverSpec (GF := GF)).objAt x o rv)
        | none => iprop(⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err)))
      $$ [] as %x %err Hr
    · iframe #
      iintro %Ψ #Hp HΨ
      wp_apply (wp_cDecode dsl DFrac.discard d) $$ [Hp Hd] as %x %g %err ⟨-, Hr⟩
      · iexact Hd
      rw [show (driverSpec (GF := GF)).objAt = objAtD from rfl,
        show (driverSpec (GF := GF)).decode = decodeObjD from rfl]
      iapply HΨ
      cases hd : decodeD d with
      | none =>
        rw [decodeObjD_none d hd]
        iexact Hr
      | some w =>
        rw [decodeObjD_of d w hd]
        icases Hr with ⟨%he, %p, %hx, Hp'⟩
        icases (typedPointsto_not_null_dup _ _ _) $$ Hp' with ⟨Hp', %hpn⟩
        isplitr
        · ipureintro; exact he
        iexists rvStr (W64 0)
        unfold objAtD
        iexists p, (W64 0)
        isplitr
        · ipureintro; exact ⟨hx, hpn, rfl⟩
        have hs := decodeD_some d w hd
        rw [DObj.ofObj_toObj_rv w hs.1 hs.2.2.2]
        iexact Hp'
    rw [show (driverSpec (GF := GF)).objAt = objAtD from rfl,
      show (driverSpec (GF := GF)).decode = decodeObjD from rfl]
    iapply HΦ
    cases decodeObjD d <;> iexact Hr
  · imodintro
    iintro %x %o %rv %Φ Ho HΦ
    rw [show (driverSpec (GF := GF)).objAt = objAtD from rfl]
    unfold objAtD
    icases Ho with ⟨%p, %n, %h, Hp⟩
    obtain ⟨rfl, hpn, rfl⟩ := h
    have hty := (objTyOk_holds).2.2
    rw [show interface.mkOk (go.GoType.PointerType objTyD) #p =
      GoInterface.ok ⟨go.GoType.PointerType objTyD, #p⟩ from rfl]
    wp_apply (wp_Annotate ⟨go.GoType.PointerType objTyD, #p⟩ (p ↦ o.toObj n) (p ↦ o.toObj n)
        (p ↦ { o.toObj n with Annotated' := true }) hty) $$ [Hp] as %err ⟨%he, HQ⟩
    · iframe Hp
      isplitl
      · iintro %Ψ Hp HΨ
        wp_apply (wp_GetAnn p (DFrac.own 1) (o.toObj n)) $$ [Hpkg Hp] as %m ⟨Hp, Hm⟩
        · iexact Hp
        iapply HΨ $$ %m Hp
        ileft
        iexact Hm
      · iintro %m %M %Ψ Hp Hm %hM HΨ
        wp_apply (wp_SetAnn p (o.toObj n) m (DFrac.own 1) M) $$ [Hpkg Hp Hm] as ⟨Hp, -⟩
        · isplitl [Hp]
          · iexact Hp
          · iexact Hm
        iapply HΨ
        rw [decide_eq_true hM]
        iexact Hp
    iapply HΦ
    isplitr
    · ipureintro; exact he
    simp only [driverW]
    iexists p, n
    isplitr
    · ipureintro; exact ⟨rfl, hpn, rfl⟩
    iexact HQ

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
