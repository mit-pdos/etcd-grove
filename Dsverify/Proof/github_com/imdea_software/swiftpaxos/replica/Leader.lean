/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Leader.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica.Leader(ballot, repNum)` (replica/replica.go:630): `ballot % int32(repNum)`; for a
non-negative ballot, a replica id `k ≥ 0` is the result iff it is the model's `leaderOf`.
(Proved here for the client handler's N4 check; `replica.go` has no frozen spec.)
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.LeaderDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.leader

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions]

theorem Leader.wp_proof : Leader.specI (hG := hG) := by
  intro b N
  wp_start as %HN
  wp_auto
  rw [if_neg (by word)]
  wp_auto
  iapply HΦ
  ipureintro
  intro hb k hk
  exact srem_leader b N HN hb k hk

end proof

end replica.leader

end Perennial.github_com.imdea_software.swiftpaxos
