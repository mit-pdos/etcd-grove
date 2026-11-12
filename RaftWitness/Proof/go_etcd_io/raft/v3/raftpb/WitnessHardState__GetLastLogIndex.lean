/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/WitnessHardState__GetLastLogIndex.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.WitnessHardState__GetLastLogIndex

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

theorem raftpb.WitnessHardState.GetLastLogIndex.wp_proof :
    raftpb.WitnessHardState.GetLastLogIndex.spec (GF := GF) (hG := hG) := by
  constructor
  · intro p dq pf v
    wp_start as ⟨%Hnn, Hf, #c⟩
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hq, %Hv⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ c
    · subst Hq
      wp_auto
      rw [show (W64 0) = v from Hv.symm]
      iapply HΦ; iexact Hf
    · wp_if_destruct
      · exact absurd rfl Hqn
      · iapply HΦ; iexact Hf
  · wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
