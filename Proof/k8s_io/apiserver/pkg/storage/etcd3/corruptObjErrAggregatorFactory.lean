/-
Lean-first (no Rocq counterpart).

The proof of `corruptObjErrAggregatorFactory`: a closure, or `defaultListErrorAggregatorFactory`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.corruptObjErrAggregatorFactory
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.defaultListErrorAggregatorFactory

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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem corruptObjErrAggregatorFactory.wp_proof
    (wp_default : defaultListErrorAggregatorFactory.spec (GF := GF) (hG := hG)) :
    corruptObjErrAggregatorFactory.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  iapply wp_fupd
  wp_auto
  cases decide (sint.Z n ≤ sint.Z (W64 0))
  · ipersist maxCount
    wp_auto
    imodintro
    iapply HΦ
    iunfold aggrFactoryOk
    iintro !> %Φ' HΦ'
    wp_auto
    wp_alloc a as Ha
    wp_auto
    iapply HΦ'
    iunfold freshAggr
    iexists ⟨go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.corruptObjErrAggregator.ty, #a⟩
    isplitr
    · ipureintro; rfl
    iintro %Ψ HΨ
    wp_method_call
    wp_call
    wp_auto
    iexact HΨ
  · wp_auto
    imodintro
    iapply HΦ
    iunfold aggrFactoryOk
    iintro !> %Φ' HΦ'
    wp_apply wp_default as %ag Hag
    iapply HΦ' $$ Hag

end proof

end k8s
end EtcdGrove
end Perennial
