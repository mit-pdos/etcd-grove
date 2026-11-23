/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ReplyDefs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**Request SWC-2, round S1** (notes/prove-swift.md "SWC-2 (round S1)"): the reply channel's
object with real content and the facts a descriptor gives `repchan.reply`.

* `swift.RCh γ γc γm rp rc bw`: **the reply-channel object** (replaces D39's `RC = fun _ => True`,
  GAP-37c). It is indexed by the epoch's ballot `bw` (the `epochRd`'s): the reply goroutine of
  the epoch of ballot `bw` (`replyChanH … bw rc`), its cell filled, and the sending context the
  goroutine needs (the sender at the replica's `N`, the `cs` codes). The run loop's `epRun` holds
  `replyChanH γ γc γm rp γl ev.bw ev.rcp ∗ cellFilled γl`, and `runPre` the sending context, so
  every descriptor of the epoch can be given `RCh … ev.rcp ev.bw`.
* `swift.exRepOk`: what the execution record must keep of each entry for the leader's reply:
  the command well formed and, at the ballot's leader, why it was executed there (the leader's
  pre-acceptance with the executed dependencies, or the ballot's `MSync`) and **the leader's
  sequence prefix** that has it, its executed dependencies a permutation of `depsIn` there.
* `swift.replyWitE`: the strengthened `replyWit` (Deliver.lean): `x` last of an execution
  `X ++ [e]` (dependencies before, no duplicates) with every entry's `exRepOk`.
* `swift.replyPre`: what the descriptor itself gives: the proposal read-only, its hashes as the
  model's, and at the leader the hashes' paths (`pathHashes`, the leader's own `pathIs`).
* `swift.replyChan.reply.specE`: `reply` over these (proved: ReplyChan.lean,
  `swift.replyChan.reply.wp_proofE`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Deliver
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ExecResult

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- An execution-record entry with model ids. -/
def swift.exY (e : swift.ExE) : sp.ExY := (toCmdId e.1, e.2.1, e.2.2.map toCmdId)

theorem swift.applyX_eq_execY (X : List swift.ExE) : swift.applyX X = sp.execY (X.map swift.exY) := by
  unfold swift.applyX sp.execY; rw [List.foldl_map]; rfl

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

/-- **The reply-channel object** (SWC-2; see the file header): replica `rp`'s reply channel `rc`
of the epoch of ballot `bw`. -/
def swift.RCh (γ : sp.Names) (γc γm : GName) (rp : Loc) (rc : Loc) (bw : w32) :
    IProp netDistGF :=
  iprop(∃ (γl : swift.CellNames) (rr s : Loc) (N : Nat) (γs : ChanNames)
      (csv : swift.CommunicationSupply),
    swift.replyChanH γ γc γm rp γl bw rc ∗ swift.cellFilled γl ∗
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.fld rr go!"N" ↦□ (W64 N) ∗
    swift.fld rp go!"sender" ↦□ s ∗ isChanBag γs s (replica.sendArgP rr γ γc γm N) ∗
    swift.fld rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv ∧ N ≤ 7⌝)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
instance swift.RCh_persistent (γ : sp.Names) (γc γm : GName) (rp rc : Loc) (bw : w32) :
    Persistent (swift.RCh γ γc γm rp rc bw) := by
  unfold swift.RCh swift.replyChanH; infer_instance

/-- **An execution-record entry's facts for the leader's reply** (SWC-2; see the file header).
`N r b`: the replica `r` of `N`, the record's epoch `b`. -/
def swift.exRepOk (γ : sp.Names) (N r b : Nat) (e : swift.ExE) : IProp netDistGF :=
  iprop(⌜e.2.1.wf⌝ ∗ (⌜r ≠ sp.leaderOf N b⌝ ∨
    ((sp.preacc γ r b (toCmdId e.1) (e.2.2.map toCmdId) ∨ swift.syncIn γ b (toCmdId e.1)) ∗
      ∃ s : sp.Seq, sp.locLb γ r b s ∗
        ⌜(toCmdId e.1, e.2.1) ∈ s ∧ (e.2.2.map toCmdId).Perm (sp.depsIn s (toCmdId e.1))⌝)))

instance swift.exRepOk_persistent (γ : sp.Names) (N r b : Nat) (e : swift.ExE) :
    Persistent (swift.exRepOk γ N r b e) := by
  unfold swift.exRepOk swift.syncIn sp.preacc sp.locLb; infer_instance

/-- **The reply's execution witness** (SWC-2; `replyWit` strengthened): `x` (dependencies `D`) is
the last command of an execution `X ++ [e]` of the record of epoch `b` of replica `r`, each
command executed after its dependencies, none twice, its result `v`, every entry with
`exRepOk`. -/
def swift.replyWitE (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (D : List swift.CommandId)
    (v : GoSlice) : IProp netDistGF :=
  iprop(∃ (X : List swift.ExE) (e : swift.ExE),
    ⌜e.1 = x ∧ e.2.2 = D ∧ swift.depsBefore (X ++ [e]) ∧ ((X ++ [e]).map Prod.fst).Nodup⌝ ∗
    v ↦*□ (state.execS e.2.1.op e.2.1.key e.2.1.val (swift.applyX X)).2 ∗
    [∗list] e' ∈ X ++ [e], swift.exRepOk γ N r b e')

instance swift.replyWitE_persistent (γ : sp.Names) (N r b : Nat) (x : swift.CommandId)
    (D : List swift.CommandId) (v : GoSlice) : Persistent (swift.replyWitE γ N r b x D v) := by
  unfold swift.replyWitE; infer_instance

/-- **What a descriptor gives `reply` for `x`** (SWC-2; persistent): the proposal read-only (its
`GPropose` and its `ClientId`, SWC-1), its hashes `dv.Hs` as the model's `Hs`, and at the
ballot `b`'s leader the paths of `Hs` (none, or the leader's own path of `x`). -/
def swift.replyPre (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV) :
    IProp netDistGF :=
  iprop(∃ (Hs : List sp.Hash) (p w mu : Loc) (addr : GoString),
    dv.propose ↦□ replica.defs.GPropose.mk p w mu false addr ∗
    typedPointsto (p.[replica.defs.Propose, go!"ClientId"]) x.ClientId' DFrac.discard ∗
    ⌜dv.Hs = Hs.map swift.handler.shashOf ∧ sp.hashesWf Hs ∧ Hs.length + 1 < 2 ^ 62 ∧
      dv.D.length < 2 ^ 62⌝ ∗
    (⌜r ≠ sp.leaderOf N b⌝ ∨ ∃ Ps : List (List sp.CmdId), sp.pathHashes Ps Hs ∗
      (⌜Ps = []⌝ ∨ ∃ P, ⌜Ps = [P]⌝ ∗ sp.pathIs γ r b (toCmdId x) P)))

instance swift.replyPre_persistent (γ : sp.Names) (N r b : Nat) (x : swift.CommandId)
    (dv : swift.DescV) : Persistent (swift.replyPre γ N r b x dv) := by
  unfold swift.replyPre sp.pathIs; infer_instance

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

/-- **`rc.reply(desc, cmdId, v)`, SWC-2's form** (`reply.specI` with real content): on the reply
channel object `RCh … rc bw` of the epoch of ballot `bw`, from `deliver` (its `descCtx`'s
replica, protocol and configuration facts, its `epochRd`'s ballot), the execution witness
`replyWitE` and the descriptor's `replyPre`, both at the replica `rid me` and the epoch
`bal bw`. -/
abbrev swift.replyChan.reply.specE : Prop :=
  ∀ (γ : sp.Names) (γc γm γl γw : GName) (rp rr : Loc) (N : Nat) (me bw : w32) (fr : Bool)
    (l : List GoString) (oe : Bool) (rc d : Loc) (γd : ChanNames) (MP : GoInterface → IProp netDistGF)
    (dv : swift.DescV) (x : swift.CommandId) (v : GoSlice),
  {{ swift.RCh γ γc γm rp rc bw ∗ swift.descF d γd MP dv ∗
      swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
      swift.fld rp go!"optExec" ↦□ oe ∗ sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗
      ⌜0 ≤ sint.Z me ∧ 0 ≤ sint.Z bw⌝ ∗
      swift.replyWitE γ N (sp.rid me) (sp.bal bw) x dv.D v ∗
      swift.replyPre γ N (sp.rid me) (sp.bal bw) x dv ∗
      □ (∀ n : w64, ⌜swift.slotIn n⌝ -∗ MP (interface.mkOk go.int #n)) }}
    (App (App (App (Val (rc @!! go.GoType.PointerType swift.replyChan.ty @!! go!"reply"))
      (Val #d)) (Val #x)) (Val #v))
  {{ RET #(); swift.descF d γd MP dv }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
