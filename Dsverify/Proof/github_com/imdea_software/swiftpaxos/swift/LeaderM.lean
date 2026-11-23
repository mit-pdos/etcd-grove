/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/LeaderM.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.leader()` (swift.go): `Leader(r.ballot, r.N)`, read with any fraction of `ballot`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BeTheLeader
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions]

theorem swift.Replica.wp_leader (wp_Leader : replica.Leader.spec) (rp rr : Loc) (b : w32)
    (q : DFrac) (N : Nat) (hN : 1 ≤ N ∧ N ≤ 7) :
    {{ (typedPointsto (swift.fld rp go!"ballot") b q : IProp netDistGF) ∗ swift.fld rp go!"Replica" ↦□ rr ∗
        replica.fld rr go!"N" ↦□ (W64 N) }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"leader")) (Val #()))
    {{ RET #(BitVec.srem b (W32 (sint.Z (W64 (N : Int))))); typedPointsto (swift.fld rp go!"ballot") b q }} := by
  wp_start as ⟨Hb, #Hrr, #HN⟩
  wp_auto
  wp_apply wp_Leader
  · ipureintro; word
  iapply HΦ
  iexact Hb

end proof

end Perennial.github_com.imdea_software.swiftpaxos
