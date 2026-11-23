/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/NewLeaderSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**Phase 4 (round N1, sv-swc): `handleNewLeader`'s state and specs** (recovery.go:15-90,
notes/prove-swift.md "Phase 4 (round N1)").

The run loop is in one of two states between the steps of `handleNewLeader`'s loop:
* normal: `swift.runInv` (RunInvD.lean; the running epoch `descDS`);
* recovering: `swift.recInv`, the same pieces with `w.2.2.1 = false` (status `RECOVERING`,
  the ballot past `cballot`) and the stopped epoch `swift.epStopped … (descDF (x.DR γ))`
  in place of `descDS` (what `handleSync.specIR` takes in recovery, SyncSpecs.lean).
`swift.runInvR s` is the one or the other (`s = true`: normal).

Specs stated here:
* `swift.Replica.handleNewLeader.specN`: from either state, to either state, never from normal
  to recovering (`s = true → s' = true`: the loop runs until `status != RECOVERING`); the
  run loop's `newLeader` arm is its instance at `s = true` (NewLeaderProof.lean).
* `swift.Replica.fillNewLeaderAckN.specN`: in recovery at ballot `bl` (cballot `cb`), the ack's
  four slices are the report `R` of the replica (`ackObj`), with `sp.reported γ r (bal bl) R`.
* `swift.Replica.handleNewLeaderAckN.specN`: in recovery, an ack `p` of a report `a` at
  ballot `bl` (`nlP`'s facts): the run loop ends in either state (the set's handler may run
  `handleNewLeaderAckNs`, which takes the new ballot's `MSync`).
* `swift.MNewLeaderAckN.marshalH`: the ack's `Marshal` (as `MNewLeader.marshalH`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunArmSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.pkg.TimeInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHashPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncTail
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecOrderDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSyncPure3
public import Perennial.Proof.slices.SortFunc
public import Perennial.Proof.math.bits.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.pdqsortCmpFuncDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.KeyDefs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Fatal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalBase

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- The stopped epoch at the run loop's names (`handleSync.specIR`'s `epStopped` as the
`sync` arm instantiates it: `DF := descDF (x.DR γ)`; round 53: `PS := swift.stopPS x`). -/
abbrev swift.epStoppedX (γ : sp.Names) (x : swift.RunX) (rp : Loc) : IProp netDistGF :=
  swift.epStopped x.syncN x.γe x.γd (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x) rp x.rr

/-- **The stopped epoch at its `cballot` `c`** (round 51, D70 (1), gap 50-1): `epStoppedX`'s body
with the epoch token's second component, the stopped epoch's `cballot` `bc.2`, exposed as `c`.
`recInvB` holds it at its `cb` (so the epoch's identity comes from an exclusive piece);
`epStoppedX` keeps hiding `bc` (`swift.epStoppedXc_forget`). -/
def swift.epStoppedXc (γ : sp.Names) (x : swift.RunX) (rp : Loc) (c : Nat) : IProp netDistGF :=
  iprop(∃ (bw : w32) (st : w64) (stp stpX : Loc) (bc : Nat × Nat),
    typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own (1 : Iris.Qp).half) ∗
    typedPointsto (swift.fld rp go!"status") st (DFrac.own (1 : Iris.Qp).half) ∗
    replica.fld x.rr go!"State" ↦ stp ∗
    (∃ rc : Loc, typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Iris.Qp).half)) ∗
    swift.epochTok x.γe (1 : Iris.Qp).half bc ∗
    ghostVar x.syncN.γxp (1 : Iris.Qp).half bc.2 ∗ ghostVar x.syncN.γxe (1 : Iris.Qp).half (bc.2, stpX) ∗
    swift.rmTok x.syncN.γrm none ∗
    swift.descsStopped x.γd (swift.descDF (x.DR γ bc.2)) (swift.stopPS x bc.2) rp ∗
    ghostMapAuth x.syncN.γout (1 : Iris.Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) ∗
    (∃ hs : w64, swift.fld rp go!"historySize" ↦ hs) ∗ swift.cntFrozen x.syncN.γn true ∗
    (∃ fq : replica.QuorumI, typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own (1 : Iris.Qp).half) ∗
      typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own (1 : Iris.Qp).half.half)) ∗
    ⌜bc.2 = c⌝)

/-- **The run loop in recovery at ballot `bl`, cballot `cb`** (see the file header): as
`runInv`, with the run loop's view recovering (`w.2.2.1 = false`) past its `cballot`, and the
stopped epoch in place of the running one. Round 51 (D70 (1)): the stopped epoch at its
`cballot` `cb` (`swift.epStoppedXc`). -/
def swift.recInvB (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (bl cb : w32) :
    IProp netDistGF :=
  iprop(swift.descCtxE γ γc γm x.γl x.γw x.γv x.γe x.γo x.γx x.γxe x.γxm x.γxp x.γxu x.γrp x.γcg x.γout x.γcl x.γdc x.γdl
      x.str rp x.rr x.N x.r x.k ∗
    swift.syncCtx γ x.N x.r x.syncN rp ∗
    swift.runLoopCtx rp γ γc γm x ∗
    (∃ (ld : Bool) (v : swift.RunV) (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView),
      swift.runSt γ x.γv rp x.N x.r ld v M bs hd w ∗ swift.propDepsOwn rp (bs ++ hd) ∗
      ⌜w.2.2.1 = false ∧ w.2.1 < w.1 ∧ v.ballot = bl ∧ v.cballot = cb ∧
        v.status = swift.stRECOVERING⌝) ∗
    swift.seqOwn γ rp x.k ∗
    swift.runReader rp x.γdl ∗
    swift.runFields γ rp x.rr x.N x.r ∗
    swift.epStoppedXc γ x rp (sint.Z cb).toNat)

/-- The run loop in recovery (at some ballot). -/
def swift.recInv (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) : IProp netDistGF :=
  iprop(∃ bl cb : w32, swift.recInvB rp γ γc γm x bl cb)

/-- The run loop normal (`s = true`) or recovering. -/
def swift.runInvR (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (s : Bool) :
    IProp netDistGF :=
  if s then swift.runInv rp γ γc γm x else swift.recInv rp γ γc γm x

/-- The post of the recovery's steps: a state, normal if the step started normal. -/
def swift.runInvP (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (s : Bool) :
    IProp netDistGF :=
  iprop(∃ s' : Bool, swift.runInvR rp γ γc γm x s' ∗ ⌜s = true → s' = true⌝)

/-- `(*MNewLeaderAckN).Marshal` (the struct read only: its owner persisted it, `ackObj`). -/
def swift.MNewLeaderAckN.marshalH : Prop :=
  ∀ (p : Loc) (a : Nat × sp.Report) (rep bl cb : w32),
    sp.Msg.wf (.newLeaderAckN rep bl cb a.2.entries) →
    -- round N3: the message's replica and cballot are the ack's (`ackObj` fixes them by their
    -- values); `state.Command`'s `Marshal` needs `encoding/binary` initialized
    sint.Z rep = a.1 → sint.Z cb = a.2.cbal →
    ⊢ isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.binary -∗
      swift.ackObj p a -∗ swift.ackBal p bl -∗
      sp.marshalOk (interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #p)
        (.newLeaderAckN rep bl cb a.2.entries) iprop(swift.ackObj p a)

/-- `epStoppedXc` forgets its `cballot` (round 51). -/
theorem swift.epStoppedXc_forget (γ : sp.Names) (x : swift.RunX) (rp : Loc) (c : Nat) :
    swift.epStoppedXc γ x rp c ⊢ swift.epStoppedX γ x rp := by
  iintro H
  iunfold swift.epStoppedXc at H
  icases H with ⟨%bw, %st, %stp, %stpX, %bc, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12,
    H13, -⟩
  iunfold swift.epStoppedX
  iunfold swift.epStopped
  iexists bw, st, stp, stpX, bc
  iframe

/-- `epStoppedX` at its `cballot` (round 51). -/
theorem swift.epStoppedX_at (γ : sp.Names) (x : swift.RunX) (rp : Loc) :
    swift.epStoppedX γ x rp ⊢ ∃ c : Nat, swift.epStoppedXc γ x rp c := by
  iintro H
  iunfold swift.epStoppedX at H
  iunfold swift.epStopped at H
  icases H with ⟨%bw, %st, %stp, %stpX, %bc, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12,
    H13⟩
  iexists bc.2
  iunfold swift.epStoppedXc
  iexists bw, st, stp, stpX, bc
  iframe
  ipureintro; rfl

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **`r.fillNewLeaderAckN(p)`** (recovery.go:417; see the file header): in recovery at ballot
`bl`, cballot `cb`, the replica's report `R` of `cb` for `bl` (its executed commands, the last
`MSync`'s, the stopped descriptors', the pending proposals; in its handled order) fills the ack's
four slices; `p` is then read-only (`ackObj`), and the report is `sp.reported` (the step
`sp.upd_report`, its witnesses from the stopped epoch). -/
abbrev swift.Replica.fillNewLeaderAckN.specN (rp : Loc) (γ : sp.Names) (γc γm : GName)
    (x : swift.RunX) : Prop :=
  ∀ (p : Loc) (rep bl cb : w32),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.recInvB rp γ γc γm x bl cb ∗
      p ↦ swift.MNewLeaderAckN.mk rep bl cb slice.nil slice.nil slice.nil slice.nil ∗
      -- round N5 (D72 (1)): `bl`'s report token (minted by `newBallot_stepD`)
      swift.repTok x.γrp (sint.Z bl).toNat ∗
      ⌜sint.Z rep = x.r⌝ }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"fillNewLeaderAckN")) (Val #p))
  {{ RET #(); swift.recInvB rp γ γc γm x bl cb ∗
      ∃ R : sp.Report, swift.ackObj p (x.r, R) ∗ swift.ackBal p bl ∗
        sp.reported γ x.r (sint.Z bl).toNat R ∗
        ⌜R.cbal = (sint.Z cb).toNat ∧ sp.Msg.wf (.newLeaderAckN rep bl cb R.entries)⌝ }}

/-- **`r.handleNewLeaderAckN(p)`** (recovery.go:67; see the file header): in recovery, an ack
`p` of replica `a.1 < N`'s report `a.2` at ballot `bl` (`nlP`'s facts). -/
abbrev swift.Replica.handleNewLeaderAckN.specN (rp : Loc) (γ : sp.Names) (γc γm : GName)
    (x : swift.RunX) : Prop :=
  ∀ (p : Loc) (a : Nat × sp.Report) (bl : w32),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.recInv rp γ γc γm x ∗
      swift.ackObj p a ∗ swift.ackBal p bl ∗ sp.reported γ a.1 (sint.Z bl).toNat a.2 ∗
      ⌜a.1 < x.N ∧ 0 ≤ sint.Z bl⌝ }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleNewLeaderAckN")) (Val #p))
  {{ RET #(); swift.runInvP rp γ γc γm x false }}

/-- **`r.handleNewLeader(l)`** (recovery.go:15; see the file header). D56 N1-b: the message's
`msgOk` (its sender `0 ≤ r < N`, the ack's destination). -/
abbrev swift.Replica.handleNewLeader.specN (rp : Loc) (γ : sp.Names) (γc γm : GName)
    (x : swift.RunX) : Prop :=
  ∀ (l : Loc) (r b : w32) (s : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.runInvR rp γ γc γm x s ∗ typedPointsto l (swift.MNewLeader.mk r b) DFrac.discard ∗
      sp.msgOk γ γc γm (.newLeader r b) }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleNewLeader")) (Val #l))
  {{ RET #(); swift.runInvP rp γ γc γm x s }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos

end
