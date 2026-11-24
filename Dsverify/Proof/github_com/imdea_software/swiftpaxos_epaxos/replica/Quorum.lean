/-
`FastQuorumSize`, `SlowQuorumSize`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.ReplicaSpec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

theorem replica.Replica.FastQuorumSize.wp_proof : replica.Replica.FastQuorumSize.spec (GF := GF) := by
  intro γ r id L p
  wp_start as #Hro
  ihave ⟨#HN, #HF, -⟩ := fwRO_fields $$ Hro
  unfold fwMethod
  wp_method_call
  wp_call
  wp_auto
  rw [show W64 2 + BitVec.sdiv (W64 2 + W64 1) (W64 2) = W64 3 by decide]
  wp_end

theorem replica.Replica.SlowQuorumSize.wp_proof : replica.Replica.SlowQuorumSize.spec (GF := GF) := by
  intro γ r id L p
  wp_start as #Hro
  ihave ⟨#HN, #HF, -, -, -, -, -, -, -, -, -, -, -, %HL⟩ := fwRO_fields $$ Hro
  rw [HL.1]
  unfold fwMethod
  wp_method_call
  wp_call
  wp_auto
  rw [show BitVec.sdiv (W64 (nRep : Int) + W64 1) (W64 2) = W64 3 by decide]
  wp_end

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
