/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E: **`node.drain`'s loop body split in
phases** (S4's `DrainPhases` over the parity vocabulary), so that `node.drain.wp_proof` (the loop,
`Ready`, the reported/silent split and the `ready` report with its write) takes the rest as two
statements proved apart:
- `drainSendB1.stmt`: the send loop (`for _, m := range rd.Messages { if early && isRequest(m) {
  continue }; n.reportCause(); n.emit(n.sendEv(by, m)); n.sendMsg(m) }`, `node.drain.sendE`), from
  the state after the report (`drainMidB1` at a view `v₁` whose pending protocol and transfer
  messages are the `Ready`'s readings, `drainMsgsB1`) to `drainMidB1` at a view with nothing pending,
  each message frozen (`drainSentB1`);
- `drainAdvanceB1.stmt`: the rest of the iteration (`node.drain.tailE`: `n.reads(rd)`,
  `n.applyCommitted(by, rd.CommittedEntries)`, `n.rn.Advance(rd)`, `for … { n.sent(m) }`), from
  `drainMidB1` with nothing pending to the next loop head (`nodeOwn … (.loop net' xnet' r' [])`, the
  `by` kept).
The fragments are `node.drain.impl`'s, its locals `n by rd early` substituted by their cells
`np bp rdp ep` (as `wp_auto` leaves them).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Send

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.raft.antithesis

/-- `drain`'s send loop (`Let "$range" …`), its locals at their cells. -/
def node.drain.sendE [GooseExts] [GoGlobalContext] (np bp rdp ep : Loc) : Expr :=
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"Messages"))) (Val #rdp)))
  (Let "m" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Val #())))
  (App (App (Val (slice.forRange (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty))) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Var "m"))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"sendMsg"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0"))))))
  (App (Val doExecute)
  (Let "$a0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Val #bp))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Var "m"))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"sendEv"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")) (Var "$a1"))))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"emit"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")))))))
  (App (Val doExecute)
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"reportCause"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Val #()))))))
  (If (If (App (Val (GoInstruction (GoLoad go.bool))) (Val #ep)) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Var "m"))
  (App (App (Val (GoInstruction (FuncResolve isRequest []))) (Val #())) (Var "$a0"))) (Val #false))
  (App (Val doContinue) (Val #()))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Pair (Var "m") (Var "$value"))))))))))

/-- `drain`'s iteration after the send loop (`n.reads(rd)`, `n.applyCommitted(by,
rd.CommittedEntries)`, `n.rn.Advance(rd)`, the `sent` loop), its locals at their cells. -/
def node.drain.tailE [GooseExts] [GoGlobalContext] (np bp rdp : Loc) : Expr :=
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"Messages"))) (Val #rdp)))
  (Let "m" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Val #())))
  (App (App (Val (slice.forRange (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty))) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Var "m"))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"sent"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0"))))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Pair (Var "m") (Var "$value"))))))))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.raft.v3.Ready.ty))) (Val #rdp))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.RawNode.ty) go!"Advance"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.RawNode.ty)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"rn"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))))) (Var "$a0")))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Val #bp))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"CommittedEntries"))) (Val #rdp)))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"applyCommitted"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.raft.v3.Ready.ty))) (Val #rdp))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"reads"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")))))

end github_com.mit_pdos.etcd_grove.examples.raft.antithesis

namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **An iteration's data**: the `RawNode` `rn`; the record `rs` and the view `v` at the loop head;
the node `r` `Ready` was taken at; the `Ready` `rd` and its outputs (`RawNode.Ready.form`'s post
at `L = none`: `ce es ms sts h steps ss W`, the queue `qs` for `Advance`, the boundary `ip` after
it). -/
structure DrainIterB1 where
  rn : Loc
  rs : RNState
  v : AntSim.NodeView
  r : RState
  rd : Ready
  ce : List EntryM
  es : List EntryM
  ms : List QMsg
  sts : List ReadStateM
  h : HardStateM
  steps : List Pending
  ss : Option (w64 × StateType)
  W : DurMaps
  qs : List Msg
  ip : Nat

/-- The record after `Ready` (no snapshot loan) and the write's handshake (`rawNode_appended`;
nothing unpersisted). -/
def DrainIterB1.rs₂ (I : DrainIterB1) : RNState :=
  { I.rs with delivered := I.rs.delivered ++ I.ce, unpersisted := [], steps := I.steps, outlb := 0,
              unst := false, phs := phsNext I.rs.phs I.h, psnap := false, slent := none,
              dur := readyDurable I.rs.dur (phsNext I.rs.phs I.h) none I.es,
              role := roleAfter I.rs.role I.ss, bw := I.W }

/-- **An iteration's pure facts**: at the loop head the record against the view (`RsView`), the
node constant the run's, the drain's `by` one of the driver's; `RawNode.Ready.form`'s `%Hout` at
`γ.R.md` (no snapshot): the queue the outbox's self-addressed messages, the `Ready`'s fields
(`ReadyOut`), the boundary at the log's end, every message a protocol or a transfer message
(protocol only at transfer off), each transfer message against the node (`XReadyOk`) with its other
numbers zero (`XZero`), the read states the node's; the term ceiling and the node's numbers within
the checker's bound (`DrainB1Bounds.rawNode_stateNums_b1`); the read states' indices within it. -/
def DrainIterB1.Ok (γ : AntNames) (j : Fin γ.R.N) (I : DrainIterB1) : Prop :=
  RsView I.rs I.v ∧ I.rs.k = γ.R.k j ∧ ByOk I.v.byE ∧
  I.qs ≡ₚ I.r.p.outbox.filter (fun m => decide (m.dst = AntSim.nodeId j)) ∧
  ReadyOut (AntSim.nodeId j) I.rs I.r.p I.h I.es I.ce I.ms I.ss none ∧
  I.ip = I.r.p.log.length ∧
  (∀ q ∈ I.ms, (absMsgOf q.st).isSome ∨ (xmsgOf q.st).isSome) ∧
  (∀ q ∈ I.ms, ∀ x, xmsgOf q.st = some x →
    XReadyOk γ.raft.raftNames γ.R.md (AntSim.nodeId j) I.r.p x ∧ XZero q.st) ∧
  (γ.R.md.transfer = false → ∀ q ∈ I.ms, (absMsgOf q.st).isSome) ∧
  I.sts = I.r.p.rd.states ∧
  uint.Z I.rs.tc < 2 ^ 61 ∧ AntSim.StateNums (2 ^ 61) I.r.p ∧
  (∀ st ∈ I.sts, uint.Z st.Index' < 2 ^ 61)

/-- **A `Ready` message's facts the send loop needs beyond the iteration's**: its term within the
ceiling (`%Hmsgs_term`), a protocol reading's numbers within the checker's bound
(`AntSim.readyMsgNums`), a forwarded `MsgTransferLeader`'s source a server (not a raft fact: the
transferee is the caller's). -/
def DrainMsgOkB1 (R : AntSim.RunCfg) (tc : w64) (q : QMsg) : Prop :=
  uint.Z q.st.msg.Term' ≤ uint.Z tc ∧
  (∀ m, absMsgOf q.st = some m → AntSim.MsgNums (2 ^ 61) m) ∧
  (∀ x, xmsgOf q.st = some x → x.ty = .transferLeader → ∃ i : Fin R.N, x.src = AntSim.nodeId i)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The iteration's state after the report** (or the silent `Ready`), at the view `vv` and the
sent lists' lower bounds `net`, `xnet`: `drain`'s cells (`n by rd`), the `RawNode` at `rs₂`
(`rAccepted r`), the loop head's rest (`loopRest`) at `vv` and `rs₂`, `Advance`'s fragments of the
durable maps (`durFrags`), the committed entries' and the read states' slices with raft's
certificates of the read states; the view the `Ready`'s (its state `accepted r`, its queue,
committed entries and read states to report, the loop head's `by`), the record against it (but the
steps `Advance` takes), its entries normal, and the iteration's facts. -/
def drainMidB1 (np bp rdp n : Loc) (γ : AntNames) (j : Fin γ.R.N) (I : DrainIterB1)
    (vv : AntSim.NodeView) (net : List Msg) (xnet : List XMsg) : IProp GF :=
  iprop(np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗
    n.[H.node, go!"rn"] ↦ I.rn ∗
    rawNode γ.raft.raftNames γ.R.md I.rn (AntSim.nodeId j) I.rs₂ (rAccepted I.r) I.qs I.ip ∗
    loopRest γ j n vv net xnet I.rs₂ ∗
    durFrags γ.raft.raftNames (AntSim.nodeId j) I.W ∗
    entsRO I.rd.CommittedEntries' I.ce ∗
    readStatesPts I.rd.ReadStates' I.sts ∗
    ([∗list] st ∈ I.sts, readStateRaw γ.raft.raftNames st) ∗
    ⌜vv.r = AntSim.accepted I.r ∧ vv.qs = I.qs ∧ vv.ce = I.ce ∧ vv.rpend = I.sts ∧
      vv.byE = I.v.byE ∧ RsView { I.rs₂ with steps := [] } vv ∧ ViewNormal vv ∧ I.Ok γ j⌝)

/-- **The `Ready`'s messages** (`RawNode.Ready.form`'s post, after `Henter`): the slice, each
message's ownership and raft's certificate (`isRaftMsg`), each one's facts (`DrainMsgOkB1`). -/
def drainMsgsB1 (γ : AntNames) (j : Fin γ.R.N) (I : DrainIterB1) : IProp GF :=
  iprop(I.rd.Messages' ↦* I.ms.map QMsg.loc ∗ ownSliceCap Loc I.rd.Messages' (DFrac.own 1) ∗
    ([∗list] q ∈ I.ms, msgOwnZ false q.loc (readyDq q.st) q.st) ∗
    ([∗list] q ∈ I.ms, isRaftMsg γ.raft.raftNames (AntSim.nodeId j) q.st) ∗
    ⌜∀ q ∈ I.ms, DrainMsgOkB1 γ.R I.rs.tc q⌝)

/-- **The `Ready`'s messages after the send loop**: the slice, each message frozen (`msgPtsC`, what
`node.sent` takes), none a snapshot. -/
def drainSentB1 (I : DrainIterB1) : IProp GF :=
  iprop(I.rd.Messages' ↦* I.ms.map QMsg.loc ∗
    ([∗list] q ∈ I.ms, msgPtsC q.loc DFrac.discard DFrac.discard false q.st) ∗
    ⌜∀ q ∈ I.ms, q.st.msg.Type' ≠ MsgSnap⌝)

/-- **The send loop** (`node.drain.sendE`, then the continuation `K`): from the state after the
report with the `Ready`'s protocol and transfer readings pending (in the messages' order), each
message reported (`reportCause`, `emit(sendEv)`) and handed over (`sendMsg`); then `K` at a view
with nothing pending, the sent lists' lower bounds grown, the messages frozen. -/
abbrev drainSendB1.stmt : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (np bp rdp ep c n : Loc) (γ : AntNames) (j : Fin γ.R.N)
    (I : DrainIterB1) (v₁ : AntSim.NodeView) (net₁ : List Msg) (xnet₁ : List XMsg) (q : Qp)
    (K : Expr) (Φ : val → IProp GF),
  v₁.pend = I.ms.filterMap (fun m => absMsgOf m.st) →
  v₁.xpend = I.ms.filterMap (fun m => xmsgOf m.st) →
  isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ ⌜DrainB1 γ.scope γ.mode⌝ ∗
      drainMidB1 np bp rdp n γ j I v₁ net₁ xnet₁ ∗ drainMsgsB1 γ j I ∗ ep ↦ false ∗
      netAdder c γ q ∗ threadTok ∗
      (∀ (v₂ : AntSim.NodeView) (net₂ : List Msg) (xnet₂ : List XMsg),
        drainMidB1 np bp rdp n γ j I v₂ net₂ xnet₂ ∗ ⌜v₂.pend = [] ∧ v₂.xpend = []⌝ ∗
          drainSentB1 I ∗ ep ↦ false ∗ netAdder c γ q ∗ threadTok -∗
          WP K {{ Φ }}) ⊢
    WP (App (App (Val exceptionSeq) (Lam BAnon K))
      (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.drain.sendE np bp rdp ep))
      {{ Φ }}

/-- **The iteration's end** (`node.drain.tailE`): from the state after the send loop (nothing
pending), the read states reported (`reads`), the committed entries reported and `n.applied` set
(`applyCommitted`), `Advance`, each message's `sent`: the next loop head (`nodeOwn … (.loop net'
xnet' r' [])`, `Reach.advance`), the `by` kept. -/
abbrev drainAdvanceB1.stmt : Prop :=
  ∀ (np bp rdp c n : Loc) (γ : AntNames) (j : Fin γ.R.N) (I : DrainIterB1) (v₂ : AntSim.NodeView)
    (net₂ : List Msg) (xnet₂ : List XMsg) (Φ : val → IProp GF),
  v₂.pend = [] → v₂.xpend = [] →
  isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ ⌜DrainB1 γ.scope γ.mode⌝ ∗
      drainMidB1 np bp rdp n γ j I v₂ net₂ xnet₂ ∗ drainSentB1 I ∗
      (∀ (v' : AntSim.NodeView) (net' : List Msg) (xnet' : List XMsg) (r' : RState),
        np ↦ n ∗ bp ↦ I.v.byE ∗ nodeOwn c γ j n v' (.loop net' xnet' r' []) ∗
          ⌜v'.byE = I.v.byE⌝ -∗ Φ executeVal) ⊢
    WP (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.drain.tailE np bp rdp)
      {{ Φ }}

end defs

end AntHarness
end EtcdGrove
end Perennial
