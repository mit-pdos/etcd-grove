/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/refused.lean` (authlease's, copied).
Lean-first (no Rocq counterpart); F7 stage S4.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.refused

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

theorem refused.wp_proof : refused.spec (GF := GF) (hG := hG) := by
  intro who what err Herr
  wp_start
  cases err with
  | nil => exact absurd rfl Herr
  | ok i =>
    wp_auto
    wp_end

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
