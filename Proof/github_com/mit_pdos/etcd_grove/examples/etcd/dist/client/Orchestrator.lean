/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/Orchestrator.lean`. Lean-first; N7-kv.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Orchestrator
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainDeployment

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]

theorem Orchestrator.wp_proofKv (OP : List GoString → w64 → IProp GF)
    (hMD : MainDeployment.specKv (GF := GF) (hG := hG) OP) :
    Orchestrator.specKv (GF := GF) (hG := hG) OP := by
  intro v d j
  wp_start as ⟨%Hp, #Hd, Hsh⟩
  wp_auto
  wp_apply (hMD v d j _) $$ [Hsh] as %r -
  · iframe #
    iframe
    isplit
    · ipureintro; exact Hp
    iunfold readySpec
    wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial
  iapply HΦ; ipureintro; trivial

end proof

end etcd_dist
end EtcdGrove
end Perennial
