/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientNodeAddr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The address helpers' instances the client node uses (`atConf.spec`, `atRpc.spec`,
`hostMaster.spec`, `portMaster.spec`, `AddrsC.spec`), from group C's `wp_at`, `wp_host`,
`wp_port`, `wp_Addrs_servers` (Proof/swiftnet/Addr.lean, any of the 13 nodes).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Addr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeShare

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions]

theorem confAddrC_atStr (c : Nat) (hc : c < 6) : confAddrC c = atStr (1 + c) (W64 2000) := by
  unfold confAddrC
  rw [List.getD_eq_getElem?_getD, atStr_cconf c hc, Option.getD_some]

theorem atConf_proof : atConf.spec := by
  intro sl dq c hc
  have hu : uint.nat (W64 1 + W64 (c : Int)) = 1 + c := by word
  have h := wp_at (GF := netDistGF) sl dq (W64 1 + W64 (c : Int)) (W64 2000) (by omega)
  rw [hu, ← confAddrC_atStr c hc] at h
  exact h

theorem startAddrC_atStr (c : Nat) (hc : c < 6) : startAddrC c = atStr (1 + c) (W64 3000) := by
  unfold startAddrC
  rw [List.getD_eq_getElem?_getD, atStr_cstart c hc, Option.getD_some]

theorem atStart_proof : atStart.spec := by
  intro sl dq c hc
  have hu : uint.nat (W64 1 + W64 (c : Int)) = 1 + c := by word
  have h := wp_at (GF := netDistGF) sl dq (W64 1 + W64 (c : Int)) (W64 3000) (by omega)
  rw [hu, ← startAddrC_atStr c hc] at h
  exact h

theorem atRpc_proof : atRpc.spec := by
  intro sl dq node h2 h6
  have hu : uint.nat (W64 6 + node) = 6 + uint.nat node := by word
  have h := wp_at (GF := netDistGF) sl dq (W64 6 + node) (W64 1000) (by omega)
  have hr := atStr_rpc (uint.nat node - 2) (by omega)
  have e : 8 + (uint.nat node - 2) = 6 + uint.nat node := by omega
  rw [e] at hr
  have hg : replicaRpcAddrs.getD (uint.nat node - 2) go!"" = atStr (6 + uint.nat node) (W64 1000) := by
    rw [List.getD_eq_getElem?_getD, hr, Option.getD_some]
  rw [hu, ← hg] at h
  exact h

theorem hostMaster_proof : hostMaster.spec := by
  have h := wp_host (GF := netDistGF) 7 go!"127.0.0.1:7001" rfl
  have e : nodeHost 7 = go!"127.0.0.1" := by decide
  rw [e] at h
  exact h

theorem portMaster_proof : portMaster.spec := by
  have h := wp_port (GF := netDistGF) 7 go!"127.0.0.1:7001" rfl
  have e : nodePort 7 = 7001 := rfl
  rw [e] at h
  exact h

theorem Addrs_proof : AddrsC.spec := wp_Addrs_servers (GF := netDistGF)

end proofs

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
