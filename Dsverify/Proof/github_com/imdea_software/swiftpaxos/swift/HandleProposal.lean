/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandleProposal.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.handleProposal(propose)` (swift.go; the run loop's propose arm), over its callees' specs
(Proof/swift/RunSpecs.lean): a proposal not seen before (`proposes`, `delivered`) is recorded,
appended to `handled` (the ghost step `upd_handle`: the replica's sequence of its ballot gets
`x`), its dependencies and path hash computed, its descriptor given the proposal with the facts
its pre-acceptance needs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

/-- `r.getCmdDescWith(x, &proposeMsg{gp, dep, hs, sq}, seq)` for a proposal the run loop handled
(`handleProposal`; P4): the message goes to `x`'s descriptor; the result is the descriptor (or
`nil` if `x` was delivered). Round 20 (sv-swb; the run-loop side's request): over the run
loop's descriptor state `DS rp` (abstract here; the instance is the descriptor side's
`getCmdDescWith` proof's: the epoch's `descStateR`, the running epoch, the persistent contexts;
`runInv` must provide it between arms) and the run loop's reader of `delivered` (for
`delivered.Has`), both given back. Round 21 (sv-swb): with a fraction of `ballot` at `b`
(handleProposal lends `runSt`'s quarter), which ties the message's ballot to the descriptors'
epoch in `DS` (`swift.descDS`, DescDS.lean). Round 28 (G7): with `handle_stepD`'s fresh row token
of `x` at the row tokens' name `γo` (a `DS` argument). Round 32 (T28): the claim `fresh` on
that token (in the store), not the token; `DS`'s name argument is now the claims' `γcl`. -/
abbrev swift.Replica.getCmdDescWith.propSpecIN (DS : sp.Names → GName → GName → Nat → Nat → Loc → IProp netDistGF) : Prop :=
  ∀ (γ : sp.Names) (γcl γdl : GName) (rp pm gp : Loc) (x : swift.CommandId) (c : sp.Cmd)
    (dep hs : GoSlice) (sq : w64) (sqb : Bool) (N r b : Nat) (ld : Bool) (s : sp.Seq)
    (B D P : List sp.CmdId) (H : swift.SHash) (bw : w32) (qb : Qp),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      DS γ γcl γdl N r rp ∗ swift.runReader rp γdl ∗ swift.propMsgR γ pm gp x c dep hs sq N r b ld s B D P H ∗
      swift.claimTok γcl (b, toCmdId x) .fresh ∗ typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) ∗ ⌜sp.bal bw = b⌝ }}
    (App (App (App
      (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDescWith")) (Val #x))
      (Val #(interface.mkOk (go.GoType.PointerType swift.proposeMsg.ty) #pm))) (Val #sqb))
  {{ (d : Loc), RET #d; DS γ γcl γdl N r rp ∗ swift.runReader rp γdl ∗
      typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) }}

/-- `propSpecIN` at a `DS` that does not depend on the protocol's names, `delivered`'s view, the replica count and id
(round 24: the descriptors' instance `swift.descDSN` does: the proposal's facts are at `γ N r`, the reader at `γdl`,
its descriptor's at the replica's own). -/
abbrev swift.Replica.getCmdDescWith.propSpecI (DS : Loc → IProp netDistGF) : Prop :=
  swift.Replica.getCmdDescWith.propSpecIN (fun _ _ _ _ _ => DS)

/-- `r.handleProposal(gp)` in normal operation (round 13, P2-B: over `swift.runCtxD` and the
run loop's own reader bundle `swift.runReader`): the run loop's state stays, its ballot,
`cballot`, normality and last `MSync` unchanged. Round 20 (sv-swb; the run-loop side's request):
the descriptors' part is the abstract `DS rp` of `getCmdDescWith.propSpecI` (passed through) and
`proposeDeps` (`swift.propDepsOwn rp`, which handleProposal writes); no more `descRun` (the old
half of `cmdDescs` with `isCMap`). Round N6 (D75 (3)): `proposeDeps` at the sequence, `bs ++ hd`
before and `bs ++ hd'` after. Round 19 (sv-swc, change log C22): the run loop's numbering
`swift.seqOwn` (its half of `seqnum`, `numHi`) in and out. -/
abbrev swift.Replica.handleProposal.specIN (DS : sp.Names → GName → GName → Nat → Nat → Loc → IProp netDistGF) : Prop :=
  ∀ (γ : sp.Names) (γc γm γl γw γv γe γo : GName) (sn : swift.StN) (γdl : GName) (rp gp : Loc)
    (N r k : Nat) (ld : Bool)
    (v : swift.RunV) (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.runCtxD γ γc γm γl γw γv γe γo sn γdl rp N r k ∗ swift.runReader rp γdl ∗
      swift.runSt γ γv rp N r ld v M bs hd w ∗ swift.seqOwn γ rp k ∗
      DS γ sn.γcl γdl N r rp ∗ swift.propDepsOwn rp (bs ++ hd) ∗ sp.proposeP γ gp ∗
      ⌜w.2.2.1 = true⌝ }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleProposal")) (Val #gp))
  {{ RET #(); ∃ (v' : swift.RunV) (hd' : sp.Seq) (w' : swift.LView),
      swift.runSt γ γv rp N r ld v' M bs hd' w' ∗ swift.seqOwn γ rp k ∗
      swift.runReader rp γdl ∗ DS γ sn.γcl γdl N r rp ∗
      swift.propDepsOwn rp (bs ++ hd') ∗ ⌜w'.1 = w.1 ∧ w'.2.1 = w.2.1 ∧ w'.2.2.1 = true⌝ }}

/-- `specIN` at a `DS` independent of `N r` (round 24). -/
abbrev swift.Replica.handleProposal.specI (DS : Loc → IProp netDistGF) : Prop :=
  swift.Replica.handleProposal.specIN (fun _ _ _ _ _ => DS)

end spec

end Perennial.github_com.imdea_software.swiftpaxos
