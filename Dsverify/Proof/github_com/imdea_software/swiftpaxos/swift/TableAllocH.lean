/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableAllocH.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`swift.tableAllocH` (Proof/swift/RunLoopSpecs.lean), proved from `swift.tableOk_alloc`
(Proof/swift/TableLink.lean): its context `swift.tbl.ctxTbl u` comes from `swift`'s package
(the readers' packages, `errVarintOverflow`: `swift.ErrVarintFact`, from the package state at the
link), the fast-ack pool's switch, gob's codec (change log C17) and the codec's obligations
(`kitCodecOk` at the linked codec, a hypothesis: `kitCodecOkC_holds` at the link).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunLoopSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

set_option linter.unusedSectionVars false

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] [replica.defs.Assumptions] [state.Assumptions] [replica.Assumptions]
  [rpc.Assumptions]
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]

/-- `errVarintOverflow` from `swift`'s package state (`swift.pkgSt`; at the link,
`isPkgInit_access` as `srv_pool_fact`). -/
abbrev swift.ErrVarintFact : Prop :=
  isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢
    errors.newVar swift.errVarintOverflow go!"binary: varint overflows a 64-bit integer"

theorem swift.tableAllocH_proof (herr : swift.ErrVarintFact (hG := hG))
    (hko : ⊢ net.rpc.kitCodecOk (GF := netDistGF))
    (wp_newFA : swift.newFastAck.specP (hG := hG))
    (wp_ND : encoding.gob.NewDecoder.spec (GF := netDistGF))
    (wp_Dec : encoding.gob.Decoder.Decode.spec (GF := netDistGF)) :
    swift.tableAllocH (hG := hG) := by
  intro γ γc γm v M u
  iintro ⟨#Hs, #Hgcs, #Hu, Hch, %Ht⟩
  ihave #Hev := herr $$ Hs
  ihave ⟨%ov, #Hov, -, %Hovn⟩ := bufio.newVar_errOrNil _ _ $$ Hev
  ihave #Hko : net.rpc.kitCodecOk (GF := netDistGF) $$ []
  · iapply hko
  iapply (swift.tableOk_alloc (wp_newFA := fun w => wp_newFA w) wp_ND wp_Dec u γ γc γm v M)
  iframe Hch
  ihave #Hio : isPkgInit (PROP := IProp netDistGF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hbuf : isPkgInit (PROP := IProp netDistGF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hbin : isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hgob : isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.gob $$ []
  · iPkgInit
  isplitl
  · unfold swift.tbl.ctxTbl swift.tbl.ctxFA swift.tbl.ctxV swift.tbl.ctxS swift.tbl.ctxIO
    iframe Hs Hu Hgcs Hko Hio Hbuf Hbin Hgob
    iexists ov
    iframe Hov
    ipureintro; exact Hovn
  · ipureintro; exact Ht

end link

end Perennial.github_com.imdea_software.swiftpaxos
