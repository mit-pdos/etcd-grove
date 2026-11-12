/-
Proof of `Spec/go_etcd_io/raft/v3/witness__isHealthy.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__isHealthy

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem witness.isHealthy.wp_proof :
    witness.isHealthy.spec (GF := GF) (hG := hG) := by
  intro w dq e
  wp_start as He
  wp_auto
  cases e with
  | nil => wp_auto; rw [decide_eq_true rfl]; iapply HΦ; iexact He
  | ok i => wp_auto; rw [decide_eq_false (by simp)]; iapply HΦ; iexact He

end proof

end EtcdGrove
end Perennial
