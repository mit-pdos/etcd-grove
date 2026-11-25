/-
Lean-first (no Rocq counterpart).

The proof of `Call`: the input's type assertion (an `Input`, `boxIn`), then `call`, its output boxed.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Call
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.call

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

theorem Call.wp_proof (wp_call : call.spec (GF := GF) (hG := hG)) :
    Call.spec (GF := GF) (hG := hG) := by
  intro _ cl ms V hAs x i Q hx hgen
  wp_start as ⟨#Hcl, #Hone, #Hregs, Hau⟩
  wp_auto
  wp_apply wp_call cl ms V hAs x i Q hx hgen $$ [Hau] as %y Hy
  · iframe Hau; iframe #
  iapply HΦ
  icases Hy with (%Hy | ⟨%σ, HQ, %Hy⟩)
  · ileft; ipureintro; subst Hy; rfl
  · iright
    iexists y, σ
    iframe HQ
    ipureintro
    exact ⟨rfl, Hy⟩

end proof

end etcd_txnlin
end EtcdGrove
end Perennial
