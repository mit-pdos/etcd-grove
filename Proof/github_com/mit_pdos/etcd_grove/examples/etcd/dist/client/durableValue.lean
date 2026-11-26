/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/durableValue.lean` (#50 N9a; restartN's
`key`/`value` proofs). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.durableValue

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

theorem durableValue.wp_proof : durableValue.spec (GF := GF) (hG := hG) := by
  intro i hi
  have h1 : sint.nat (W64 (0 + 1)) = 1 := by word
  have h2 : (((sint.nat i : Nat) : Int)) = sint.Z i := by unfold sint.nat; exact Int.toNat_of_nonneg hi
  wp_start as -
  wp_auto
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sl ⟨Hsl, -⟩
  (try wp_auto)
  wp_apply (wp_bytes_to_string _ _ _) $$ [Hsl] as -
  (try iexact Hsl)
  (try wp_auto)
  iapply HΦ
  ipureintro
  unfold durVal
  rw [h2]
  (try rw [h1])
  (try rfl)
  (try simp)

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
