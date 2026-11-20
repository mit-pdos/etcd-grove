/- Lean-first (no Rocq counterpart).

The proof of `keyFunc`: the type assertion to `*Obj` succeeds, then `storeKey`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyFunc
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem keyFunc.wp_proof (wp_storeKey : storeKey.spec (GF := GF) (hG := hG)) :
    keyFunc.spec (GF := GF) (hG := hG) := by
  intro x o
  wp_start as ⟨#Hx⟩
  iunfold deepRep at Hx
  icases Hx with ⟨%p, %hx, #Hp⟩
  subst hx
  iStructNamed Hp
  wp_auto
  wp_apply wp_storeKey
  iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
