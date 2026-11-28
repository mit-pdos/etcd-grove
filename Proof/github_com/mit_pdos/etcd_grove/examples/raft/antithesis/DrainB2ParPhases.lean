/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **`node.parallel`'s fragments**
(`DrainB1Phases`' `node.drain.sendE` pattern): `node.parallel.impl`'s request loop (`reqE`: `for _, m
:= range rd.Messages { if isRequest(m) { n.reportCause(); n.emit(n.sendEv(by, m)); n.sendMsg(m) } }`)
and its write (`writeE`: `if write { … n.announce(n.stateEv("write", hs, rd.Entries));
n.saveDisk(whs, rd.Entries); n.emit(wrote); n.storeSave(whs, rd.Entries); n.hs = hs }`), its locals
`n rd by hs write` substituted by their cells `np rdp bp hsp wrp` (as `wp_auto` leaves them);
and the request loop's statement (`parReqB2.stmt`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Phases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Send

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.raft.antithesis

/-- `parallel`'s request loop (`Let "$range" …`), its locals at their cells. -/
def node.parallel.reqE [GooseExts] [GoGlobalContext] (np rdp bp : Loc) : Expr :=
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"Messages"))) (Val #rdp)))
  (Let "m" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Val #())))
  (App (App (Val (slice.forRange (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty))) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Var "m"))
  (App (App (Val (GoInstruction (FuncResolve isRequest []))) (Val #())) (Var "$a0")))
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
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"reportCause"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Val #()))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Message.ty)))) (Pair (Var "m") (Var "$value"))))))))))

/-- `parallel`'s write (`If write …`), its locals at their cells. -/
def node.parallel.writeE [GooseExts] [GoGlobalContext] (np rdp hsp wrp : Loc) : Expr :=
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Val #wrp))
  (Let "whs" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Val #hsp))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"hs"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$r0")))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Var "whs"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"Entries"))) (Val #rdp)))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"storeSave"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoAlloc _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event.ty))) (Let "$v0" (Val #(go!"wrote"))
  (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event.ty))) (LiteralValue [(KeyedElement (some (KeyField go!"E")) (ElementExpression go.string (Var "$v0")))]))))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"emit"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Var "whs"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"Entries"))) (Val #rdp)))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"saveDisk"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (Let "$a0" (Let "$a0" (Val #(go!"write"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Val #hsp))
  (Let "$a2" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"Entries"))) (Val #rdp)))
  (App (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"stateEv"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"announce"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Val #hsp)) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"hs"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))))))))
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Val #hsp))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Pair (Var "whs") (Var "$r0")))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (Val #())))

end github_com.mit_pdos.etcd_grove.examples.raft.antithesis
end Perennial

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The cause cell on the request loop's way** (alive: against the view, with the sent lists' lower
bounds; dead: some pending report, which `reportCause` drops). -/
def parCauseB2 (γ : AntNamesB2) (j : Fin γ.R.N) (dead : Bool) (v : AntSim.NodeView) (cl : Loc)
    (net : List Msg) (xnet : List XMsg) : IProp GF :=
  if dead then iprop(∃ o : Option AntCheck.Event, pendingCause cl o)
  else iprop(causeOwn γ.toAntNames j v cl ∗ sentLb γ.toAntNames net ∗ xsentLb γ.toAntNames xnet)

/-- **`parallel`'s request loop** (`node.parallel.reqE`, then the continuation `K`), at a mask `msk`
within B2's that the run's relation admits, synchronous storage without batching: from the view `v₁`
with the requests (appends and heartbeats) pending first (`reqPend … 0`, alive), each request
reported (`reportCause`, `emit(sendEv)`: `sendHstepD`) and handed over (`sendMsg`), each other message
left; a kill on the way (`emit`'s fuse) leaves the rest unreported and unsent. Then `K` at the view
`v₂`, `v₁` but for its pending messages (alive: the other messages, `reqPend … ms.length`), `told` (set
once the cause is reported: a `Ready` without requests whose `mem` was not reported reports none) and
the undo record (none and made once a request is reported); the requests frozen (`drainMsgsParB2`). -/
abbrev parReqB2.stmt : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (np rdp bp c n : Loc) (γ : AntNamesB2) (j : Fin γ.R.N)
    (I : DrainIterB1) (msk : AntSim.SimMask) (v₁ : AntSim.NodeView) (net₁ : List Msg)
    (xnet₁ : List XMsg) (dead : Bool) (fuse : w64) (cl : Loc) (q : Qp) (K : Expr) (Φ : val → IProp GF),
  msk ≤ AntSim.mskB2 →
  (∀ S V net xnet, AntSim.AntSimD γ.R γ.dec S V net xnet → AntSim.InMask msk γ.R net xnet) →
  γ.R.md.async = false → γ.R.drv.batch = false →
  I.OkB2 γ.toAntNames j → (dead = false → v₁.pend = reqPend I.ms 0 ∧ v₁.parts = []) →
  isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ ⌜DrainB2 γ.scope γ.mode⌝ ∗
      np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗ killOwn n dead fuse ∗ n.[H.node, go!"cause"] ↦ cl ∗
      viewFrag γ.toAntNames j v₁ ∗ parCauseB2 γ j dead v₁ cl net₁ xnet₁ ∗ rnTermLB γ.raft I.rs.tc ∗
      I.rd.Messages' ↦* I.ms.map QMsg.loc ∗ ownSliceCap Loc I.rd.Messages' (DFrac.own 1) ∗
      ([∗list] m ∈ I.ms, msgOwnZ false m.loc (readyDq m.st) m.st) ∗
      ([∗list] m ∈ I.ms, isRaftMsg γ.raft.raftNames (AntSim.nodeId j) m.st) ∗
      ⌜∀ m ∈ I.ms, DrainMsgOkB1 γ.R I.rs.tc m⌝ ∗
      runLive γ q ∗ netAdder c γ.toAntNames q ∗ threadTok ∗
      (∀ (dead' : Bool) (fuse' : w64) (cl' : Loc) (v₂ : AntSim.NodeView) (net₂ : List Msg)
          (xnet₂ : List XMsg),
        np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗ killOwn n dead' fuse' ∗ n.[H.node, go!"cause"] ↦ cl' ∗
          viewFrag γ.toAntNames j v₂ ∗ parCauseB2 γ j dead' v₂ cl' net₂ xnet₂ ∗
          ⌜(dead = true → dead' = true) ∧ net₁ <+: net₂ ∧ xnet₁ <+: xnet₂ ∧
            (∃ (P : List Msg) (T : Bool) (U : Option AntSim.DurW) (M : Bool),
              v₂ = { v₁ with pend := P, told := T, undo := U, made := M } ∧
              ((U = v₁.undo ∧ M = v₁.made) ∨ (U = none ∧ M = true)) ∧ (T = v₁.told ∨ T = true) ∧
              (dead' = false → P = reqPend I.ms I.ms.length))⌝ ∗
          drainMsgsParB2 γ j I ∗ runLive γ q ∗ netAdder c γ.toAntNames q ∗ threadTok -∗
          WP K {{ Φ }}) ⊢
    WP (App (App (Val exceptionSeq) (Lam BAnon K))
      (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.parallel.reqE np rdp bp))
      {{ Φ }}

end defs

end AntHarness
end EtcdGrove
end Perennial
