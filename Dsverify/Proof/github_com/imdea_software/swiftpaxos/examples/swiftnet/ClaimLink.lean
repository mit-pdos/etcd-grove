/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClaimLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2's claim (`client.claimGhost.spec`) at the run's package states: `ClaimHyp` (ServersLink.lean),
the client nodes' and the server nodes' L2 hypothesis, proved (`claim_hyp`); and the client nodes'
taking of their fresh ghost (`client_fresh`, B's `cnode.Callees.fresh`; decision D90, R-E1).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Claim
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeNew

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [GoGlobalContext]

/-- **The claim at the run's package states** (`client.claimGhost.wp_proof`; the `sync`
package's Goose assumptions from the node's `examples.swiftnet.Assumptions`). -/
theorem claim_hyp : ClaimHyp := by
  intro hG s _
  letI := @pkgStates _ netDistGF hG s
  exact client.claimGhost.wp_proof

/-- Client node `c`'s own address (`clientNodeAddrs[c]`) is `ip:7000` for its configured IP
`ip`, which is not a replica node's. -/
theorem clientIp_key (c : Nat) (ip : IPv4) (hc : c < 6)
    (hip : swiftNetCfg.ips[1 + c]? = some ip) :
    client.keyAddr ip.spell = clientNodeAddrs.getD c go!"" ∧ ¬ swift.replicaNode ip.spell := by
  match c, hc, hip with
  | 0, _, h | 1, _, h | 2, _, h | 3, _, h | 4, _, h | 5, _, h =>
    simp only [swiftNetCfg, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at h
    subst h
    unfold client.keyAddr swift.replicaNode
    decide

/-- **On client node `c`, its own address token takes its fresh ghost** (B's
`cnode.Callees.fresh`): `client.ghostFresh_take` at the run's package states. -/
theorem client_fresh (hG : HeapGS .hasLC netDistGF) (s : go.Semantics) (c : Nat) (ip : IPv4)
    (hc : c < 6) (hip : swiftNetCfg.ips[1 + c]? = some ip)
    (hnet : netIp (L := hG.goose_localGS) (GF := netDistGF) = ip.spell) :
    letI := @pkgStates _ netDistGF hG s
    cnode.freshTake.spec (hG := hG) c := by
  letI := @pkgStates _ netDistGF hG s
  obtain ⟨hk, hrn⟩ := clientIp_key c ip hc hip
  unfold cnode.freshTake.spec
  rw [← hk, ← hnet]
  apply client.ghostFresh_take
  · with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client
  · rw [hnet]; exact hrn

end link

end Perennial.github_com.imdea_software.swiftpaxos
