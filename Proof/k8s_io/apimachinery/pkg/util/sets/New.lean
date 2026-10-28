/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/sets/New.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

theorem New.wp_proof (wp_Insert : Set.Insert.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro K _ _ _ _ T _ _ sl dq ks
  wp_start as Hsl
  (try wp_auto)
  rw [go.make2_underlying, (go.is_underlying : underlying (Set'.ty T) = _)]
  wp_apply (wp_map_make2 (K := K) (V := Elem) _ T Empty.ty) as %r Hr
  (try wp_auto)
  wp_apply (Set.wp_ptr_Insert_of wp_Insert) $$ [$ss $Hr $Hsl] as ⟨ss, Hr, Hsl⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end sets
end EtcdGrove
end Perennial
