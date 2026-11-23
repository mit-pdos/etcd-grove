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

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleMsg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- **`proposeCtx` without its take law** (round 37; table rev 8 G-ctx, plan R8b.1 (3)): the base
fields a proposal's handling reads (`ackCtx`, `slowAddrs`, `fastRead` with the configuration,
`useFastAckPool`); `proposeCtx c` (HandleProposeProof.lean) is it with `takeLaw c`
(`swift.proposeCtx_ofB`). Below the owner records (DescKind's `ownCtx` holds it). -/
def swift.proposeCtxB (c : swift.DC) : IProp netDistGF :=
  iprop(swift.ackCtx c ∗
    ∃ (sam : GoMap) (fr : Bool) (lg : List GoString) (v : Bool),
      swift.fld c.rp go!"slowAddrs" ↦□ sam ∗ sam ↦$□ (∅ : GMap GoString Unit) ∗
      swift.fld c.rp go!"fastRead" ↦□ fr ∗ sp.cfg c.γc c.γm c.N fr lg ∗
      globalAddr swift.useFastAckPool ↦□ v)

instance swift.proposeCtxB_persistent (c : swift.DC) : Persistent (swift.proposeCtxB c) := by
  unfold swift.proposeCtxB; infer_instance

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- **`r.handlePropose(pm, desc, cmdId)`** (see the file header). -/
abbrev swift.Replica.handlePropose.specIc (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF) (c : swift.DC) : Prop :=
  ∀ (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (pm gp : Loc) (cc : sp.Cmd) (dep hs : GoSlice) (sq : w64) (ld : Bool) (s : sp.Seq)
    (B D P : List sp.CmdId) (H : swift.SHash),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ □ AC c ∗ swift.descOwnF c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do) ∗
      swift.propMsgR c.γ pm gp x cc dep hs sq c.N c.r b ld s B D P H ∗
      swift.claimTok c.γcl (b, toCmdId x) .fresh }}
    (App (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handlePropose"))
      (Val #pm)) (Val #d)) (Val #x))
  {{ RET #(); (swift.descOwnF c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do) ∨ swift.descDone c b x d) }}

/-- `swift.Replica.handlePropose.specI` at every record (round 44, D53 (1): the per-record form `swift.Replica.handlePropose.specIc`). -/
abbrev swift.Replica.handlePropose.specI (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF) : Prop :=
  ∀ c : swift.DC, swift.Replica.handlePropose.specIc RC MP AC c

/-- `r.handleMsg(&proposeMsg{…}, desc, cmdId)`: `handlePropose`'s. Round 32 (table rev 5 T11₀, D6):
the message carries the `fresh` claim; round 34 (table rev 6, G-slot): `handlePropose` takes the
token out of the store where it installs it (:512, `install_tok` with `takeLaw`). -/
abbrev swift.Replica.handleMsg.propSpecIc (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF) (c : swift.DC) : Prop :=
  ∀ (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (pm gp : Loc) (cc : sp.Cmd) (dep hs : GoSlice) (sq : w64) (ld : Bool) (s : sp.Seq)
    (B D P : List sp.CmdId) (H : swift.SHash),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ □ AC c ∗ swift.descOwnF c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do) ∗
      swift.propMsgR c.γ pm gp x cc dep hs sq c.N c.r b ld s B D P H ∗
      swift.claimTok c.γcl (b, toCmdId x) .fresh }}
    (App (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
      (Val #(interface.mkOk (go.GoType.PointerType swift.proposeMsg.ty) #pm))) (Val #d)) (Val #x))
  {{ RET #false; (swift.descOwnF c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do) ∨ swift.descDone c b x d) }}

/-- `swift.Replica.handleMsg.propSpecI` at every record (round 44, D53 (1): the per-record form `swift.Replica.handleMsg.propSpecIc`). -/
abbrev swift.Replica.handleMsg.propSpecI (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF) : Prop :=
  ∀ c : swift.DC, swift.Replica.handleMsg.propSpecIc RC MP AC c

end specs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions] [hook.Assumptions]

/-- `phaseWhy` reads only `phase` and `D` (round 33). -/
theorem swift.phaseWhy_congr (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv dv' : swift.DescV)
    (h1 : dv'.phase = dv.phase) (h2 : dv'.D = dv.D) :
    swift.phaseWhy γ N r b x dv ⊢ swift.phaseWhy γ N r b x dv' := by
  unfold swift.phaseWhy; rw [h1, h2]

/-- `depWhy` reads only `phase`, `D` and `propose` (round 33). -/
theorem swift.depWhy_congr (γ : sp.Names) (γxm : GName) (N r b : Nat) (x : swift.CommandId) (dv dv' : swift.DescV)
    (h1 : dv'.phase = dv.phase) (h2 : dv'.D = dv.D) (h3 : dv'.propose = dv.propose) :
    swift.depWhy γ γxm N r b x dv ⊢ swift.depWhy γ γxm N r b x dv' := by
  unfold swift.depWhy; rw [h1, h2, h3]

/-- The owner's frame `A` out of the owner state (and back). -/
theorem swift.descOwn_frame (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (A Do : IProp netDistGF) :
    swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ (A ∗ Do)) ⊢
      A ∗ (A -∗ swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ (A ∗ Do))) := by
  unfold swift.descOwn
  iintro ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS, HR⟩
  iunfold swift.setR at HR
  iunfold swift.descSt at HR
  icases HR with ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, #Hra, %Hph,
    #Hpw, #Hdw, %Hrp, #HsB, ⟨HsF, HfF, HdF, ⟨Hcore, ⟨HA, HDo⟩⟩⟩⟩
  iframe HA
  iintro HA
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS
  iunfold swift.setR
  iunfold swift.descSt
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh Hrd HRC Hd Htok Hcom Hra HsF HfF HdF Hcore HA HDo Hpw Hdw HsB
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp

end lemmas

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
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
