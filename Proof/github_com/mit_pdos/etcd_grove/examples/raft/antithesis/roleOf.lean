/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/roleOf.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.roleOf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

theorem roleOf.wp_proof : roleOf.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  wp_if_destruct
  · rw [show roleStr (W64 2) = go!"leader" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show roleStr (W64 1) = go!"candidate" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show roleStr (W64 3) = go!"precandidate" by decide]
    iapply HΦ
    ipureintro; trivial
  rw [show roleStr s = go!"follower" by
    simp only [roleStr, StateLeader, StateCandidate, StatePreCandidate]; simp_all]
  iapply HΦ
  ipureintro; trivial

end proof

end AntHarness
end EtcdGrove
end Perennial
