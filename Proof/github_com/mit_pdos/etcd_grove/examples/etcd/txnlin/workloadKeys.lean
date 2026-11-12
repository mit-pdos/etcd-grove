/-
Lean-first (no Rocq counterpart).

The proof of `workloadKeys`: the slice literal.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.workloadKeys

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

theorem workloadKeys.wp_proof : workloadKeys.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (l := wks)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hs, Hc⟩
  wp_auto
  iapply HΦ
  iframe

end proof

end etcd_txnlin
end EtcdGrove
end Perennial
