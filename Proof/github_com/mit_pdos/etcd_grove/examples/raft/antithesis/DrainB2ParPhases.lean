/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **`node.parallel`'s fragments**
(`DrainB1Phases`' `node.drain.sendE` pattern): `node.parallel.impl`'s request loop (`reqE`: `for _, m
:= range rd.Messages { if isRequest(m) { n.reportCause(); n.emit(n.sendEv(by, m)); n.sendMsg(m) } }`)
and its write (`writeE`: `if write { … n.announce(n.stateEv("write", hs, rd.Entries));
n.saveDisk(whs, rd.Entries); n.emit(wrote); n.storeSave(whs, rd.Entries); n.hs = hs }`), its locals
`n rd by hs write` substituted by their cells `np rdp bp hsp wrp` (as `wp_auto` leaves them).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Phases

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
