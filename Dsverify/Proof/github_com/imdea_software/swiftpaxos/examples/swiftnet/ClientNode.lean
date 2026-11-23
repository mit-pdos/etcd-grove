/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientNode.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`ClientNodeOk`** (Spec/swiftnet/Interface.lean) for any package states `S`, from the specs of
the client node's callees that other groups own (`Callees`, at every local ghost state and Go
context of a client node): the client package's (`NewClientLog`, `NewBufferClient`,
`Connect`/`Disconnect` at the codec `kitCodecC` (decision D6), `Write`, `Read`), the swift
package's `NewClient`, the test package's initialization, `registerRPC`,
the registration step `client.claimGhost.spec` (L2's; `awaitConf` is group C's
`wp_awaitConf_client`). `Addrs`, `at`, `host`, `port` are group C's proofs (ClientNodeAddr.lean),
`NewBeTheLeaderReply` the defs package's, the codec's obligations `kitCodecOkC_holds`.

The choices (`ClientNodeSpec`): `is_sys := isSys γ c`, `client_tok := clientTok γ c`
(ClientNodeDefs.lean); `tok_advance` is `clientTok_advance`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeAddr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

-- The codec of the linked results (decision D6, Proof/swiftnet/KitLike.lean): `kitCodecC`,
-- whose `kitCodecOk` holds (`kitCodecOkC_holds`).
attribute [local instance 2000] examples.swiftnet.kitCodecC

namespace cnode

section hyps
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions] [io.ExtraAssumptions]

/-- The client node's callees' specs owned by other groups (or other files), at client node
`c`'s `HeapGS` and package states. -/
structure Callees (c : Nat) : Prop where
  /-- the test package's initialization (group C) -/
  init : ∀ (get_is_pkg_init : GoString → IProp netDistGF),
    GetIsPkgInitProp kit.pkg get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val kit.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp netDistGF) kit.pkg }}
  /-- `registerRPC()` -/
  reg : registerRPC.spec (GF := netDistGF)
  /-- the client package (group E) -/
  ncl : client.NewClientLog.spec
  nbc : client.NewBufferClient.spec
  conn : client.BufferClient.Connect.specG
  disc : client.BufferClient.Disconnect.specG
  write : client.BufferClient.Write.spec
  read : client.BufferClient.Read.spec
  /-- the swift package -/
  nc : swift.NewClient.spec
  /-- the node's registration step (L2's, used by group C's `wp_awaitConf_client`) -/
  claim : client.claimGhost.spec
  /-- the node's own address token takes its fresh ghost from the client package's state
  (L2's, decision D90 R-E1) -/
  fresh : freshTake.spec c

end hyps

theorem clientNodes_lookup {c : Nat} {nd : Node} [GoGlobalContext]
    (h : clientNodes[c]? = some nd) : c < 6 ∧ nd = clientNodeAt c := by
  unfold clientNodes at h
  simp only [List.getElem?_map] at h
  by_cases hc : c < 6
  · rw [List.getElem?_range hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨hc, h.symm⟩
  · rw [List.getElem?_eq_none (by simp; omega)] at h
    simp at h

/-- The callees' specs at every client node's local ghost state and Go context (client node `c`
on its configured IP), for the package states `S`. -/
def ClientNodeHyps [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] (S : SwiftNetPkgStates) :
    Prop :=
  ∀ (hG : HeapGS .hasLC netDistGF) (s : go.Semantics), hG.goose_globalGS = G →
    ∀ [examples.swiftnet.Assumptions] [net.FieldAssumptions] [io.ExtraAssumptions],
    ∀ (c : Nat) (ip : IPv4), c < 6 → swiftNetCfg.ips[1 + c]? = some ip →
      netIp (L := hG.goose_localGS) (GF := netDistGF) = ip.spell →
    letI := @S netDistGF hG s
    Callees c

/-- **`ClientNodeOk`**, from the callees' specs. -/
def client_node_ok_of [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]
    (S : SwiftNetPkgStates) (H : ClientNodeHyps S) : ClientNodeOk S := by
  intro γ c nd hG s hnd hGG hA ip hip hnet
  obtain ⟨hc, rfl⟩ := clientNodes_lookup hnd
  obtain ⟨hA1, hA2, hA3⟩ := hA
  letI := @S netDistGF hG s
  have hH := H hG s hGG c ip hc hip hnet
  subst hGG
  have wp_connect := Sys.connect.wp_proof γ c hc hostMaster_proof portMaster_proof hH.ncl hH.nbc hH.conn hH.disc
    hH.nc
  have wp_leaders := Sys.changeLeaders.wp_proof γ c atRpc_proof replica.defs.wp_NewBeTheLeaderReply
  exact {
    is_sys := isSys γ c
    is_sys_persistent := fun sys => isSys_persistent γ c sys
    client_tok := clientTok γ c
    wp_initialize' := hH.init
    wp_NewClient := NewClient.wp_proof γ c hc Addrs_proof atConf_proof hH.claim
      hH.fresh hH.reg
      wp_leaders kitCodecOkC_holds
    wp_Op := fun sys j i hj hpre =>
      Op.wp_proof γ c wp_connect hH.write hH.read sys j i
        (by have : uint.nat kit.k = 8 := rfl; omega) hpre
    tok_advance := fun sys j j' h => clientTok_advance γ c sys j j' h }

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
