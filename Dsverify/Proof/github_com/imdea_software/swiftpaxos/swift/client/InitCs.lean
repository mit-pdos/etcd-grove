/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/InitCs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`initCs(cs, t)` (swift/defs.go:301) on the client's `CommunicationSupply` and a fresh table
(`fastrpc.NewTableId(defs.RPC_TABLE)`): fourteen buffered channels, registered in the table
from id 9 in order (`Spec/swift/Wire.lean`'s `Msg.code`). What the client uses: the channels of
the seven `select` cases of `handleMsgs` (fresh, buffered, empty) and the table's entries for the
three client messages (10, 12, 15).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.TableC
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandlerState
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.InitCsDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.rd

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions] [time.Assumptions]

set_option goose.wp.extras true

theorem initCs.wp_proof : initCs.specI (hG := hG) := by
  intro cs t v
  wp_start as ⟨Hcs, Ht⟩
  wp_auto
  mk_ch HfFA
  mk_ch HfFAC
  mk_ch Hx3
  mk_ch HfLSA
  mk_ch HfAk
  mk_ch HfOA
  mk_ch HfR
  mk_ch Hx8
  mk_ch Hx9
  mk_ch Hx10
  mk_ch Hx11
  mk_ch Hx12
  mk_ch Hx13
  mk_ch HfA
  reg_one
  reg_one
  reg_one
  reg_one
  reg_one
  reg_one
  reg_one
  reg_one
  reg_one
  reg_one
  reg_one
  reg_one
  reg_one
  reg_one
  iapply HΦ
  iexists _, _, _
  isplitl [Hcs]
  · iexact Hcs
  isplitl [Ht]
  · iexact Ht
  isplitl [HfR]
  · iexact HfR
  isplitl [HfFAC]
  · iexact HfFAC
  isplitl [HfLSA]
  · iexact HfLSA
  isplitl [HfA]
  · iexact HfA
  isplitl [HfFA]
  · iexact HfFA
  isplitl [HfAk]
  · iexact HfAk
  isplitl [HfOA]
  · iexact HfOA
  ipureintro
  refine ⟨?_, ?_, ?_⟩ <;>
    simp (config := { decide := true }) only [GMap.lookup_insert_eq_iff, ↓reduceIte] <;>
    exact ⟨_, rfl⟩

end proof

end swift.rd

end Perennial.github_com.imdea_software.swiftpaxos
