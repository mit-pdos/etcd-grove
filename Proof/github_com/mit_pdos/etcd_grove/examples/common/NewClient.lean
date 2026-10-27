/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/NewClient.lean` (2026-10-22, D33;
over `NewClients` since 2026-10-23). Lean-first (no Rocq counterpart).

The endpoints' slice literal (read-only from here on), then `NewClients`, whose result is
returned.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem NewClient.wp_proof
    (wp_NewClients : NewClients.spec (GF := GF) (hG := hG)) :
    NewClient.spec (GF := GF) (hG := hG) := by
  intro addr lg V Hlg Hpl Htb
  wp_start
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  wp_apply (wp_NewClients _ [addr] lg V Htb Hlg (plainEndpoints_singleton _ Hpl)) $$ []
    as %cl %cerr Hcl
  · iframe #
  (try wp_auto)
  iapply HΦ
  iexact Hcl

end proof

end common
end EtcdGrove
end Perennial
