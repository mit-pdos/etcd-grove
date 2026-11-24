/-
Lean-first (no Rocq counterpart). #33 S4: **`Cluster.drain`'s loop body split in phases**, so that
the proof (`Cluster__drain.lean`: the loop, `Ready`, the `ready` report and the write) takes the rest
as two statements proved apart:
- `drainSend.stmt`: the send loop (`for _, m := range rd.Messages { reportCause; record(send); send }`,
  `Cluster.drain.sendE`), from the state after the write (`drainMid` at the view `v₁` whose `pend`
  are the `Ready`'s messages, `drainMsgs`) to `drainMid` at a view with nothing pending;
- `drainAdvance.stmt`: the rest of the iteration (`Cluster.drain.tailE`: the `apply` report if there
  are committed entries, `n.applied`, `Advance`), from `drainMid` with nothing pending to the next
  loop head (`nodeOwn … (.loop net' ps')`, the `by` kept).
The fragments are `Cluster.drain.impl`'s, its locals `c n by rd` substituted by their cells
`cp np bp rdp` (as `wp_auto` leaves them).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainLoop
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShapeStmt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgBounds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.raft.antithesis

/-- `drain`'s send loop (`Let "$range" …`), its locals at their cells. -/
def Cluster.drain.sendE [GooseExts] [GoGlobalContext] (cp np bp rdp : Loc) : Expr :=
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"Messages"))) (Val #rdp)))
    (Let "m" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Val #())))
    (App (App (Val (slice.forRange (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty))) (Var "$range"))
    (Lam "$key"
    (Lam "$value"
    (App (App (Val exceptionSeq) (Lam BAnon
    (App (App (Val exceptionSeq) (Lam BAnon
    (App (App (Val exceptionSeq) (Lam BAnon
    (App (App (Val exceptionSeq) (Lam BAnon
    (App (Val doExecute)
    (Let "$a0" (App (Val (GoInstruction (TypeAssert (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty) _root_.Perennial.google_golang_org.protobuf.proto.Message.ty))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Var "m")))
    (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.google_golang_org.protobuf.proto.Clone []))) (Val #())) (Var "$a0"))))
    (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Cluster.ty) go!"send"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Cluster.ty)))) (Val #cp))) (Var "$a0"))))))
    (App (Val doExecute)
    (Let "$a0" (App (Val (GoInstruction (GoAlloc _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event.ty))) (Let "$v0" (Val #(go!"send"))
    (Let "$v1" (App (Val (GoInstruction (GoLoad go.string))) (App (Val (GoInstruction (StructFieldRef node.ty go!"name"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))))
    (Let "$v2" (App (Val (GoInstruction (GoOp GoOr go.uint32))) (Pair (Val #(W32 1)) (Val #(W32 8192))))
    (Let "$v3" (App (Val (GoInstruction (GoLoad go.string))) (Val #bp))
    (Let "$v4" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Var "m"))
    (Let "$a1" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty) go!"GetTo"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Var "m"))) (Val #()))
    (App (App (App (Val (GoInstruction (FuncResolve msgOf []))) (Val #())) (Var "$a0")) (Var "$a1"))))
    (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event.ty))) (LiteralValue [(KeyedElement (some (KeyField go!"E")) (ElementExpression go.string (Var "$v0"))), (KeyedElement (some (KeyField go!"Node")) (ElementExpression go.string (Var "$v1"))), (KeyedElement (some (KeyField go!"Has")) (ElementExpression go.uint32 (Var "$v2"))), (KeyedElement (some (KeyField go!"By")) (ElementExpression go.string (Var "$v3"))), (KeyedElement (some (KeyField go!"Msg")) (ElementExpression _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.ty (Var "$v4")))]))))))))
    (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Recorder.ty) go!"record"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Recorder.ty)))) (App (Val (GoInstruction (StructFieldRef Cluster.ty go!"rec"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Cluster.ty)))) (Val #cp))))) (Var "$a0")))))))
    (App (Val doExecute)
    (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))
    (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Cluster.ty) go!"reportCause"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Cluster.ty)))) (Val #cp))) (Var "$a0")))))))
    (App (Val doExecute)
    (Var "$key")))))
    (App (Val doExecute)
    (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Pair (Var "m") (Var "$value"))))))))))

/-- `drain`'s iteration after the send loop (the `apply` report, `Advance`), its locals at their
cells. -/
def Cluster.drain.tailE [GooseExts] [GoGlobalContext] (cp np bp rdp : Loc) : Expr :=
  (App (App (Val exceptionSeq) (Lam BAnon
    (App (Val doExecute)
    (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.raft.v3.Ready.ty))) (Val #rdp))
    (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.RawNode.ty) go!"Advance"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.RawNode.ty)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"rn"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))))) (Var "$a0"))))))
    (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"CommittedEntries"))) (Val #rdp)))
    (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))]))) (Val #())) (Var "$a0"))) (Val #(W64 0)))))
    (App (App (Val exceptionSeq) (Lam BAnon
    (App (App (Val exceptionSeq) (Lam BAnon
    (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty) go!"GetIndex"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty)))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"CommittedEntries"))) (Val #rdp))) (App (Val (GoInstruction (GoOp GoSub go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"CommittedEntries"))) (Val #rdp)))
    (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))]))) (Val #())) (Var "$a0"))) (Val #(W64 1)))))))) (Val #()))
    (App (Val doExecute)
    (App (Val (GoInstruction (GoStore go.uint64))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"applied"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$r0")))))))
    (App (Val doExecute)
    (Let "$a0" (App (Val (GoInstruction (GoAlloc _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event.ty))) (Let "$v0" (Val #(go!"apply"))
    (Let "$v1" (App (Val (GoInstruction (GoLoad go.string))) (App (Val (GoInstruction (StructFieldRef node.ty go!"name"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))))
    (Let "$v2" (App (Val (GoInstruction (GoOp GoOr go.uint32))) (Pair (App (Val (GoInstruction (GoOp GoOr go.uint32))) (Pair (Val #(W32 1)) (Val #(W32 32)))) (Val #(W32 64))))
    (Let "$v3" (App (Val (GoInstruction (GoLoad go.string))) (Val #bp))
    (Let "$v4" (App (Val (GoInstruction (Convert go.uint64 go.int))) (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty) go!"GetIndex"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty)))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"CommittedEntries"))) (Val #rdp))) (Val #(W64 0)))))) (Val #())))
    (Let "$v5" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"CommittedEntries"))) (Val #rdp)))
    (App (App (Val (GoInstruction (FuncResolve entriesOf []))) (Val #())) (Var "$a0")))
    (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event.ty))) (LiteralValue [(KeyedElement (some (KeyField go!"E")) (ElementExpression go.string (Var "$v0"))), (KeyedElement (some (KeyField go!"Node")) (ElementExpression go.string (Var "$v1"))), (KeyedElement (some (KeyField go!"Has")) (ElementExpression go.uint32 (Var "$v2"))), (KeyedElement (some (KeyField go!"By")) (ElementExpression go.string (Var "$v3"))), (KeyedElement (some (KeyField go!"First")) (ElementExpression go.int (Var "$v4"))), (KeyedElement (some (KeyField go!"Entries")) (ElementExpression (go.GoType.SliceType _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry.ty) (Var "$v5")))])))))))))
    (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Recorder.ty) go!"record"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Recorder.ty)))) (App (Val (GoInstruction (StructFieldRef Cluster.ty go!"rec"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Cluster.ty)))) (Val #cp))))) (Var "$a0")))))))
    (App (Val doExecute)
    (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))
    (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Cluster.ty) go!"reportCause"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Cluster.ty)))) (Val #cp))) (Var "$a0")))))
    (App (Val doExecute)
    (Val #()))))

end github_com.mit_pdos.etcd_grove.examples.raft.antithesis

namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **An iteration's data**: the `RawNode` `rn`; the record `rs` and the view `v` at the loop head;
the state `ps₁` `Ready` was taken at; the `Ready` `rd` and its outputs (`RawNode.Ready.form`'s post:
`h es ce ms ss steps W`, the queue `qs` for `Advance`, the boundary `ip` after it). -/
structure DrainIter where
  rn : Loc
  rs : RNState
  v : AntSim.NodeView
  ps₁ : PState
  rd : Ready
  h : HardStateM
  es : List EntryM
  ce : List EntryM
  ms : List QMsg
  ss : Option (w64 × StateType)
  steps : List Pending
  W : DurMaps
  qs : List Msg
  ip : Nat

/-- The record after `Ready` and the write's handshake (`rawNode_appended`; no snapshot). -/
def DrainIter.rs₂ (I : DrainIter) : RNState :=
  { I.rs with delivered := I.rs.delivered ++ I.ce, unpersisted := [], steps := I.steps, outlb := 0,
              unst := false, phs := phsNext I.rs.phs I.h, psnap := false, slent := none,
              dur := readyDurable I.rs.dur (phsNext I.rs.phs I.h) none I.es,
              role := roleAfter I.rs.role I.ss, bw := I.W }

/-- **An iteration's pure facts**: at the loop head the record against the view (`RsView`), nothing
committed unreported, the `Ready`'s fields (`ReadyOut`, no snapshot), its queue the outbox's
self-addressed messages, the boundary at the log's end; the drain's `by` one of the harness's. -/
def DrainIter.Ok (id : w64) (I : DrainIter) : Prop :=
  RsView I.rs I.v ∧ I.v.ce = [] ∧ ReadyOut id I.rs I.ps₁ I.h I.es I.ce I.ms I.ss none ∧
  I.qs ≡ₚ I.ps₁.outbox.filter (fun m => decide (m.dst = id)) ∧ I.ip = I.ps₁.log.length ∧
  ByOk I.v.byE

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The iteration's state after the write**, at the view `vv` and the sent list's lower bound
`net`: `drain`'s cells (`c n by rd`), the `RawNode` at `rs₂` (`pAccepted ps₁`), the loop head's rest
(`loopRest`) at `vv`, `Advance`'s fragments of the durable maps (`durFrags`), the committed entries'
slice; the view the `Ready`'s (its state `pAccepted ps₁`, its queue, its committed entries, the loop
head's delivered entries and `by`), and the iteration's facts. -/
def drainMid (cp np bp rdp c n : Loc) (γ : AntNames) (j : Fin 3) (I : DrainIter)
    (vv : AntSim.NodeView) (net : List Msg) : IProp GF :=
  iprop(cp ↦ c ∗ np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗
    n.[H.node, go!"rn"] ↦□ I.rn ∗
    rawNode γ.raft.raftNames I.rn (AntSim.nodeId j) I.rs₂ (pAccepted I.ps₁) I.qs I.ip ∗
    loopRest γ j n vv net I.rs₂ ∗
    durFrags γ.raft.raftNames (AntSim.nodeId j) I.W ∗
    entsRO I.rd.CommittedEntries' I.ce ∗
    ⌜vv.ps = pAccepted I.ps₁ ∧ vv.qs = I.qs ∧ vv.ce = I.ce ∧ vv.delivered = I.v.delivered ∧
      vv.byE = I.v.byE ∧ I.Ok (AntSim.nodeId j)⌝)

/-- A `Ready` message's facts (`q`, read `m`): its reading, to another node, a voter, of the drain's
shape (`ReadyMsgShape`), its numbers within the bound if not a proposal, its term within the
ceiling. -/
def DrainMsgOk (id : w64) (tc : w64) (q : QMsg) (m : Msg) : Prop :=
  absMsgOf q.st = some m ∧ q.st.msg.To' ≠ id ∧ AntSim.ReadyMsgShape id m ∧
  (m.ty ≠ .propose → AntSim.MsgNums (2 ^ 61) m) ∧ (∃ j : Fin 3, m.dst = AntSim.nodeId j) ∧
  uint.Z q.st.msg.Term' ≤ uint.Z tc

/-- **The `Ready`'s messages** (`RawNode.Ready.form`'s post, after `Henter`): the slice, each
message's ownership and raft's certificate (`isRaftMsg`), each read as the view's pending message in
order (`DrainMsgOk`). -/
def drainMsgs (γ : AntNames) (j : Fin 3) (I : DrainIter) (vv : AntSim.NodeView) : IProp GF :=
  iprop(I.rd.Messages' ↦* I.ms.map QMsg.loc ∗ ownSliceCap Loc I.rd.Messages' (DFrac.own 1) ∗
    ([∗list] q ∈ I.ms, msgOwnZ false q.loc (readyDq q.st) q.st) ∗
    ([∗list] q ∈ I.ms, isRaftMsg γ.raft.raftNames (AntSim.nodeId j) q.st) ∗
    ⌜List.Forall₂ (DrainMsgOk (AntSim.nodeId j) I.rs.tc) I.ms vv.pend⌝)

/-- **The send loop** (`Cluster.drain.sendE`, then the continuation `K`): from the state after the
write with the `Ready`'s messages pending, each reported (`reportCause`, `record`) and handed over
(`proto.Clone`, `send`); then `K` at a view with nothing pending, the sent list's lower bound grown. -/
abbrev drainSend.stmt : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (cp np bp rdp c n : Loc) (γ : AntNames) (j : Fin 3) (I : DrainIter)
    (v₁ : AntSim.NodeView) (net₀ : List Msg) (q : Qp) (K : Expr) (Φ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO γ n j ∗ drainMid cp np bp rdp c n γ j I v₁ net₀ ∗
      drainMsgs γ j I v₁ ∗ netAdder c γ q ∗ threadTok ∗
      (∀ (v₂ : AntSim.NodeView) (net₂ : List Msg),
        drainMid cp np bp rdp c n γ j I v₂ net₂ ∗ ⌜v₂.pend = []⌝ ∗ netAdder c γ q ∗ threadTok -∗
          WP K {{ Φ }}) ⊢
    WP (App (App (Val exceptionSeq) (Lam BAnon K))
      (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.drain.sendE cp np bp rdp))
      {{ Φ }}

/-- **The iteration's end** (`Cluster.drain.tailE`): from the state after the send loop (nothing
pending), the committed entries reported (`reportCause`, `record`; `n.applied` set), `Advance`: the
next loop head (`nodeOwn … (.loop net' ps')`: `rsView_next`, `reach_next`), the `by` kept. -/
abbrev drainAdvance.stmt : Prop :=
  ∀ (cp np bp rdp c n : Loc) (γ : AntNames) (j : Fin 3) (I : DrainIter) (v₂ : AntSim.NodeView)
    (net₂ : List Msg) (Φ : val → IProp GF),
  v₂.pend = [] →
  isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO γ n j ∗ drainMid cp np bp rdp c n γ j I v₂ net₂ ∗
      (∀ (v' : AntSim.NodeView) (net' : List Msg) (ps' : PState),
        cp ↦ c ∗ np ↦ n ∗ bp ↦ I.v.byE ∗ nodeOwn c γ j n v' (.loop net' ps') ∗
          ⌜v'.byE = I.v.byE⌝ -∗ Φ executeVal) ⊢
    WP (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.drain.tailE cp np bp rdp)
      {{ Φ }}

end defs

end AntHarness
end EtcdGrove
end Perennial
