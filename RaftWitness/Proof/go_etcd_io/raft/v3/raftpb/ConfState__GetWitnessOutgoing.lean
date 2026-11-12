/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfState__GetWitnessOutgoing.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetWitnessOutgoing

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

theorem raftpb.ConfState.GetWitnessOutgoing.wp_proof :
    raftpb.ConfState.GetWitnessOutgoing.spec (GF := GF) (hG := hG) := by
  intro p pw dq Hnn
  wp_start as ⟨Hf, #cW⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  ihave (⟨%Hq, -⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ cW
  · subst Hq
    wp_auto
    iapply HΦ
    iexact Hf
  · wp_if_destruct
    · exact absurd rfl Hqn
    · iapply HΦ
      iexact Hf

end proof

end EtcdGrove
end Perennial
