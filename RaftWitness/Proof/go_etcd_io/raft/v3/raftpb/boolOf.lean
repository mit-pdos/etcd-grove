/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/boolOf.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.boolOf

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

theorem raftpb.boolOf.wp_proof : raftpb.boolOf.spec (GF := GF) (hG := hG) := by
  intro p v
  wp_start as #Hc
  ihave (⟨%Hp, %Hv⟩ | ⟨#Hq, %Hpn⟩) := cellRO_cases $$ Hc
  · subst Hp
    wp_auto
    rw [show false = v from Hv.symm]
    iapply HΦ; itrivial
  · wp_auto
    wp_if_destruct
    · exact absurd rfl Hpn
    · iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
