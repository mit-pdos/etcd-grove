/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandlePropose.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.handlePropose(pm, desc, cmdId)` (swift.go; P4, fork e411c02) by `x`'s descriptor's owner in
epoch `b` (round 13, notes/prove-swift.md §19): the spec, and the proof of its P4 prefix
(the proposal message's dependencies, hashes and number set by the owner).

* `swift.descRest c b x d`: the owner's fields outside `descOwnF`'s: `proposeDep`, `seqnum`,
  the owner's half of `hs`, and who set them (`swift.pdOk`).
* `swift.Replica.handlePropose.specI`: from the owner state (`descOwnF` with `descRest` in its
  frame), the epoch pin and a proposal message of `x` handled by this replica in `b`
  (`propMsgR`), the owner state back or the descriptor retired.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleMsgDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposeDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [hook.Assumptions]

end specs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

end lemmas

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [hook.Assumptions]

/-- `handleMsg`'s proposal case (over `handlePropose`'s spec). -/
theorem swift.Replica.handleMsg.wp_proofProp (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF)
    (str0 : swift.CommandId → GoString)
    (wp_hp : ∀ c : swift.DC, c.str = str0 → RC = swift.RCh c.γ c.γc c.γm c.rp →
      swift.Replica.handlePropose.specIc RC MP AC c) :
    ∀ c : swift.DC, c.str = str0 → RC = swift.RCh c.γ c.γc c.γm c.rp →
      swift.Replica.handleMsg.propSpecIc RC MP AC c := by
  intro c hc hRCe γd d x b Do pm gp cc dep hs sq ld s B D P H
  wp_start as ⟨#Hctx, #Hack, Hown, Hm, Hnt⟩
  wp_auto
  -- T11₀ (table rev 6, G-slot): the claim goes to `handlePropose`, whose `install_tok` (:512)
  -- takes the token out of the store (`takeLaw`)
  wp_apply (wp_hp c hc hRCe γd d x b Do pm gp cc dep hs sq ld s B D P H) $$ [Hown Hm Hnt] as Hres
  · iframe Hctx Hack Hown Hm Hnt
  try wp_auto
  iapply HΦ; iexact Hres

end proof

end Perennial.github_com.imdea_software.swiftpaxos
