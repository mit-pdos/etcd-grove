/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`swift.tableOk_alloc`**: the run loop's table, from `initCs`'s channels and entries, is
`sp.tableOk` with the bags `swift.csBags` (the representation `swift.msgRep`), under the
persistent facts `swift.tbl.ctxTbl v` (the packages, `errVarintOverflow`, the fast-ack pool's
switch `useFastAckPool ↦□ v`, the gob model's codec). The callees in other groups are
hypotheses (their frozen or stated specs): `newFastAck` (the coordinator's `specP`), gob's
`NewDecoder`, `Decode`, `state.Value.Unmarshal` (the replica group's). The element decoders'
specs (`MFastAck`, `Ack`, `SDep`) are hypotheses of `tableOk_alloc_h`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableAlloc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableOptAcks
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableClient
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableAckN
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableFastAck
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableAck
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.ProposeUnmarshal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

set_option linter.unusedSectionVars false

namespace swift.tbl

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] [replica.defs.Assumptions] [state.Assumptions]

/-- The persistent facts of the table's entries. -/
def ctxTbl (v : Bool) : IProp netDistGF :=
  iprop(ctxFA v ∗ ctxS ∗ ctxIO)

instance ctxTbl_persistent (v : Bool) : Persistent (ctxTbl (hG := hG) v) := by
  unfold ctxTbl; infer_instance

theorem ctxTbl_V (v : Bool) : ctxTbl (hG := hG) v ⊢ ctxV := by
  unfold ctxTbl ctxFA; iintro ⟨⟨#H, -⟩, -⟩; iexact H

theorem ctxTbl_FA (v : Bool) : ctxTbl (hG := hG) v ⊢ ctxFA v := by
  unfold ctxTbl; iintro ⟨#H, -⟩; iexact H

theorem ctxTbl_S (v : Bool) : ctxTbl (hG := hG) v ⊢ ctxS := by
  unfold ctxTbl; iintro ⟨-, #H, -⟩; iexact H

theorem ctxTbl_IO (v : Bool) : ctxTbl (hG := hG) v ⊢ ctxIO := by
  unfold ctxTbl; iintro ⟨-, -, #H⟩; iexact H

theorem tableOk_alloc_h (wp_FA : MFastAck.Unmarshal.specS (hG := hG))
    (wp_Ack : Ack.Unmarshal.specS (hG := hG)) (wp_SDep : SDep.Unmarshal.specS (hG := hG))
    (wp_newFA : newFastAck.specP' (hG := hG))
    (wp_ND : encoding.gob.NewDecoder.spec (GF := netDistGF))
    (wp_Dec : encoding.gob.Decoder.Decode.spec (GF := netDistGF))
    (wp_Val : state.Value.Unmarshal.spec (GF := netDistGF))
    (v : Bool) (γ : sp.Names) (γc γm : GName) (csv : swift.CommunicationSupply)
    (M : GMap w8 rpc.Pair') :
    ctxTbl v ∗ swift.csChans csv ∗ ⌜swift.tableIs csv M⌝ ⊢
      |={⊤}=> ∃ n : swift.CsNames, sp.tableOk γ γc γm M ∗ swift.csBags γ γc γm csv n := by
  apply tableOk_alloc_of (ctxTbl v) γ γc γm csv M
  · intro o; exact (ctxTbl_FA v).trans (newOk_fastAck wp_FA wp_newFA v o)
  · intro o; exact (ctxTbl_V v).trans (newOk_fastAckClient o)
  · intro o; iintro -; iapply newOk_MSlowAck o
  · intro o; exact (ctxTbl_IO v).trans (newOk_lightSlowAck o)
  · intro o; exact (ctxTbl_V v).trans (newOk_acks wp_FA o)
  · intro o; exact (ctxTbl_V v).trans (newOk_optAcks wp_Ack o)
  · intro o; exact (ctxTbl_V v).trans (newOk_reply o)
  · intro o; exact (ctxTbl_IO v).trans (newOk_newLeader o)
  · intro o; exact (ctxTbl_V v).trans (newOk_newLeaderAckN wp_SDep wp_Val o)
  · intro o; exact (ctxTbl_S v).trans (newOk_sync wp_ND wp_Dec o)
  · intro o; iintro -; iapply newOk_MPing o
  · intro o; iintro -; iapply newOk_MPingRep o
  · intro o; iintro -; iapply newOk_MCollect o
  · intro o; iintro -; iapply newOk_MAccept o

/-- **The table's allocation**, the element decoders linked. -/
theorem _root_.Perennial.github_com.imdea_software.swiftpaxos.swift.tableOk_alloc
    (wp_newFA : newFastAck.specP' (hG := hG))
    (wp_ND : encoding.gob.NewDecoder.spec (GF := netDistGF))
    (wp_Dec : encoding.gob.Decoder.Decode.spec (GF := netDistGF))
    (v : Bool) (γ : sp.Names) (γc γm : GName) (csv : swift.CommunicationSupply)
    (M : GMap w8 rpc.Pair') :
    ctxTbl v ∗ swift.csChans csv ∗ ⌜swift.tableIs csv M⌝ ⊢
      |={⊤}=> ∃ n : swift.CsNames, sp.tableOk γ γc γm M ∗ swift.csBags γ γc γm csv n :=
  tableOk_alloc_h MFastAck.Unmarshal.wp_proof Ack.Unmarshal.wp_proof SDep.Unmarshal.wp_proof
    wp_newFA wp_ND wp_Dec state.Value.Unmarshal.wp_proof v γ γc γm csv M

end link

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
