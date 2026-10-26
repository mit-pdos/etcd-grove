/-
Lean-first (no Rocq counterpart).

The proof of `(*store).Delete`: the prepared key, `conversion.EnforcePtr(out)` (the object is a
non-nil pointer of the store's type), the feature gate (whatever it answers, the caller's option
is `false`), then `conditionalDelete`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Delete
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__prepareKey
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__conditionalDelete
public import Spec.k8s_io.apimachinery.pkg.conversion.EnforcePtr
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.Delete.wp_proof
    (wp_prepareKey : store.prepareKey.spec (GF := GF) (hG := hG))
    (wp_EnforcePtr : conversion.EnforcePtr.spec (GF := GF) (hG := hG))
    (wp_condDelete : store.conditionalDelete.spec (GF := GF) (hG := hG)) :
    store.Delete.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ E _ sp c ci cd key out o0 rv0 opts validate vf W _ Φu k hk hopt
  wp_start as ⟨#Hst, #Hctx, #Hce, Hout, HW, #Hau, #Hval⟩
  ihave Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt,
    #Hkc, #Hcl, #Hone, #Hregs, #Hcon⟩
  iunfold contractOk at Hcon
  icases Hcon with ⟨%Hty, -⟩
  ihave #Pcv : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.conversion $$ []
  · iPkgInit
  ihave #Pft : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.util.feature $$ []
  · iPkgInit
  ihave #Hft : (k8s_io.apiserver.pkg.storage.etcd3.featureInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pft
  icases Hft with ⟨%g, #Hg, #Hen⟩
  ihave %Hptr := c.S.objAt_ptr out o0 rv0 $$ Hout
  obtain ⟨p, hp, rfl⟩ := Hptr
  (try wp_auto)
  wp_apply wp_prepareKey sp c.resourcePrefix c.pathPrefix key false $$ [] as %pk %perr %Hpk
  · iframe #
  rw [hk] at Hpk
  obtain ⟨rfl, rfl⟩ := Hpk
  (try wp_auto)
  wp_apply wp_EnforcePtr c.S.objTy p $$ [] as %v %eerr %Hen'
  · iframe #
    ipureintro; exact hp
  obtain ⟨rfl, Hv⟩ := Hen'
  (try wp_auto)
  have hnp : k8s_io.apiserver.pkg.features.AllowUnsafeMalformedObjectDeletion.isPanic = false :=
    features.AllowUnsafeMalformedObjectDeletion_notPanic
  wp_pure
  (try wp_auto)
  have hpfx : c.pfx <+: c.pathPrefix ++ k := prepareKeyM_prefix _ _ _ _ _ hk
  wp_apply Hen as %b
  cases b <;>
  · (try wp_auto)
    (try rw [hopt])
    (try wp_auto)
    wp_apply (wp_condDelete Obj E sp c ci cd (c.pathPrefix ++ k)
        (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o0 rv0 v p validate vf W Φu hpfx)
        $$ [$Hout $HW] as %err Hres
    · iframe #
      ipureintro; exact Hv
    (try wp_auto)
    iapply HΦ
    iexact Hres

end proof

end k8s
end EtcdGrove
end Perennial
