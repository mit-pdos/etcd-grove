/-
Lean-first (no Rocq counterpart).

The proof of `IsWrite`: `isWrite`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.IsWrite
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.isWrite

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

theorem IsWrite.wp_proof (wp_isWrite : isWrite.spec (GF := GF) (hG := hG)) :
    IsWrite.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_isWrite x
  iapply HΦ; itrivial

end proof

end etcd_txnlin
end EtcdGrove
end Perennial
