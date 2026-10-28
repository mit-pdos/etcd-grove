/-
**A `*DaemonSet`'s `GetNamespace()` and `GetName()`** through its `metav1.Object` methods, at any
fraction (lemmas over the accessors' specs, hypotheses `hget`): what the key functions of
`tools/cache` read of the DaemonSet controller's objects. Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.ObjLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode apimodel

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [meta_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]
variable [apps_sem : k8s_io.api.apps.v1.Assumptions]

/-- **`GetName()` on a DaemonSet held at any fraction**: the name, the DaemonSet back. -/
theorem dsAt_GetName (hget : metav1.ObjectMeta.GetName.spec (GF := GF) (hG := hG))
    (l : Loc) (dq : DFrac) (dd : kd.apps.DaemonSet) :
    {{ dsAt (GF := GF) l dq dd }}
      (App (Val #(methods (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) go!"GetName" #l))
        (Val #()))
    {{ RET #dd.ObjectMeta'.Name'; dsAt l dq dd }} := by
  wp_start as Ho
  simp only [dsAt]
  icases Ho with ⟨%v, Hl, Hd⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  icases kd.apps.DaemonSet.own_meta _ _ _ $$ Hd with ⟨Hm, Hback⟩
  ihave %Hb := meta_own_base _ _ _ $$ Hm
  wp_apply (hget _ v.ObjectMeta' dq) $$ [ObjectMeta] as ObjectMeta
  · iexact ObjectMeta
  ihave Hd := Hback $$ %v.ObjectMeta' %dd.ObjectMeta' [Hm]
  · iexact Hm
  rw [Hb.1]
  iapply HΦ
  iexists v
  iframe Hd
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- **`GetNamespace()` on a DaemonSet held at any fraction**: the namespace, the DaemonSet
back. -/
theorem dsAt_GetNamespace (hget : metav1.ObjectMeta.GetNamespace.spec (GF := GF) (hG := hG))
    (l : Loc) (dq : DFrac) (dd : kd.apps.DaemonSet) :
    {{ dsAt (GF := GF) l dq dd }}
      (App (Val #(methods (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) go!"GetNamespace" #l))
        (Val #()))
    {{ RET #dd.ObjectMeta'.Namespace'; dsAt l dq dd }} := by
  wp_start as Ho
  simp only [dsAt]
  icases Ho with ⟨%v, Hl, Hd⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  icases kd.apps.DaemonSet.own_meta _ _ _ $$ Hd with ⟨Hm, Hback⟩
  ihave %Hb := meta_own_base _ _ _ $$ Hm
  wp_apply (hget _ v.ObjectMeta' dq) $$ [ObjectMeta] as ObjectMeta
  · iexact ObjectMeta
  ihave Hd := Hback $$ %v.ObjectMeta' %dd.ObjectMeta' [Hm]
  · iexact Hm
  rw [Hb.2.2.1]
  iapply HΦ
  iexists v
  iframe Hd
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end lemmas

end cache
end EtcdGrove
end Perennial
