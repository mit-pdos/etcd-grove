/-
Lean-first (no Rocq counterpart).

The proof of `getTypeName`: `reflect.TypeOf(obj).String()`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.getTypeName
public import Spec.reflect.TypeOf

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem getTypeName.wp_proof (wp_TypeOf : reflect.TypeOf.spec (GF := GF) (hG := hG)) :
    getTypeName.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start as %Hx
  ihave #Pr : isPkgInit (PROP := IProp GF) pkg_id.reflect $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_TypeOf x $$ [] as %t #Ht
  · iframe #
    ipureintro; exact Hx
  wp_apply Ht as %s -
  iapply HΦ
  itrivial

end proof

end k8s
end EtcdGrove
end Perennial
