/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E (the synchronous `node.drain`): **the
write of a `Ready` that is not a `-parallel` leader's** and the Sim steps the drain needs that the B2 Sim
statements (`Sim/StmtsB2`) do not have yet, statements only (round 20: nothing proves them yet):
- `node.drain.syncBodyE`: `drain`'s `else if write || role != n.role { … }` branch body (`n.reportCause()`;
  `write`: per part `announce(withByRole(stateEv("ready", p.after, p.ents), by, role))`, `saveDisk`,
  `storeSave`, `n.hs = p.after`; else `emit(…("ready", hs, nil)…)`; `n.role = role`), its locals `n by rd hs
  write role` at their cells `np bp rdp hsp wrp rlp`;
- `drainSyncB2.stmt`: that branch, its condition evaluated (`b`), from the state right after the `Ready`
  (`drainPreB2`) to the state after the write (`drainMidB2`) with the messages owned (`drainMsgsB1`), or
  dead (`nodeOwnB2HD … .drained none true`): `node.parallel.spec`'s post for the other `Ready`s;
- `antSim_noReadyD_in.law`: `QuietIn.noReady` (`HasReady` false at the loop head) over `AntSimD`;
- `antSim_silentD_in.law`: `QuietIn.silentReady` (a `Ready` the harness does not report, not a
  `-parallel` leader's: those go through `antSim_quietP_in`) over `AntSimD`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Tail

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.raft.antithesis

/-- `drain`'s `else if write || role != n.role` branch body, its locals at their cells. -/
def node.drain.syncBodyE [GooseExts] [GoGlobalContext] (np bp rdp hsp wrp rlp : Loc) : Expr :=
(App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Val #rlp))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"role"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$r0")))))))
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Val #wrp))
  (Let "$range" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Val #hsp))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.go_etcd_io.raft.v3.Ready.ty go!"Entries"))) (Val #rdp)))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"parts"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")) (Var "$a1"))))
  (Let "p" (App (Val (GoInstruction (GoAlloc part.ty))) (App (Val (GoInstruction (GoZeroVal part.ty))) (Val #())))
  (App (App (Val (slice.forRange part.ty)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (App (Val (GoInstruction (StructFieldRef part.ty go!"after"))) (Var "p")))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"hs"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$r0")))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (App (Val (GoInstruction (StructFieldRef part.ty go!"hs"))) (Var "p")))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef part.ty go!"ents"))) (Var "p")))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"storeSave"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (App (Val (GoInstruction (StructFieldRef part.ty go!"hs"))) (Var "p")))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef part.ty go!"ents"))) (Var "p")))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"saveDisk"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (Let "$a0" (Let "$a0" (Let "$a0" (Val #(go!"ready"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (App (Val (GoInstruction (StructFieldRef part.ty go!"after"))) (Var "p")))
  (Let "$a2" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (App (Val (GoInstruction (StructFieldRef part.ty go!"ents"))) (Var "p")))
  (App (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"stateEv"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Val #bp))
  (Let "$a2" (App (Val (GoInstruction (GoLoad go.string))) (Val #rlp))
  (App (App (App (App (Val (GoInstruction (FuncResolve withByRole []))) (Val #())) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"announce"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")))))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore part.ty))) (Pair (Var "p") (Var "$value"))))))))))
  (App (Val doExecute)
  (Let "$a0" (Let "$a0" (Let "$a0" (Val #(go!"ready"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.HardState.ty)))) (Val #hsp))
  (Let "$a2" (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.raftpb.Entry.ty))))) (Val UntypedNil))
  (App (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"stateEv"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Val #bp))
  (Let "$a2" (App (Val (GoInstruction (GoLoad go.string))) (Val #rlp))
  (App (App (App (App (Val (GoInstruction (FuncResolve withByRole []))) (Val #())) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"emit"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0"))))))))
  (App (Val doExecute)
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"reportCause"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Val #()))))

end github_com.mit_pdos.etcd_grove.examples.raft.antithesis

namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **A loop head with no `Ready` over the B2 relation** (`QuietIn.noReady`, `antSim_quiet_in`'s case
over `AntSimD`; synchronous storage, no batching, no `mem` queued, no split write): the node's view
takes raft's state, which has the view's hard state, role and full log, nothing to send or read. -/
abbrev antSim_noReadyD_in.law : Prop :=
  ∀ (msk : AntSim.SimMask), msk ≤ AntSim.mskB2 →
  ∀ (R : AntSim.RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
    (net : List Msg) (xnet : List XMsg) (G : AntSim.RaftFacts) (n : Fin R.N) (r₁ : RState)
    (Adm : List EntryM → CCState → Prop),
    AntSim.InMask msk R net xnet → AntSim.AntSimD R dec S V net xnet → AntSim.RaftLaws G →
    AntSim.GlobalOk R S net G → R.md.async = false → R.drv.batch = false →
    (V n).mems = [] → (V n).parts = [] →
    AntSim.ReachIn msk R dec Adm net xnet n (V n) r₁ → r₁.p.outbox = [] → r₁.p.rd.states = [] →
    r₁.p.term = (V n).ps.term → r₁.p.vote = (V n).ps.vote → r₁.p.commit = (V n).ps.commit →
    r₁.p.role = (V n).ps.role → r₁.full = (V n).r.full →
    AntSim.AntSimD R dec S (AntSim.setV V n { V n with r := r₁, qs := [] }) net xnet

/-- **A synchronous `Ready` the harness does not report over the B2 relation** (`QuietIn.silentReady`
over `AntSimD`: no write, the same role; not a `-parallel` leader's, whose requests go first,
`antSim_quietP_in`): the drain phase, its messages pending in their order. -/
abbrev antSim_silentD_in.law : Prop :=
  ∀ (msk : AntSim.SimMask), msk ≤ AntSim.mskB2 →
  ∀ (R : AntSim.RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
    (net : List Msg) (xnet : List XMsg) (G : AntSim.RaftFacts) (n : Fin R.N) (r₁ : RState)
    (rd : AntSim.ReadyD) (Adm : List EntryM → CCState → Prop),
    AntSim.InMask msk R net xnet → AntSim.AntSimD R dec S V net xnet → AntSim.RaftLaws G →
    AntSim.GlobalOk R S net G → R.md.async = false → R.drv.batch = false →
    (V n).mems = [] → (V n).parts = [] →
    AntSim.ReachIn msk R dec Adm net xnet n (V n) r₁ → AntSim.ReadyOutP R n (V n) r₁ rd →
    ¬ (R.drv.parallel = true ∧ rd.role = .leader) → rd.snap = none → ¬ AntSim.Reported (V n) rd →
    AntSim.ReadyFacts G (AntSim.nodeId n) r₁ →
    AntSim.AntSimD R dec S (AntSim.setV V n ((V n).drainOf r₁ rd)) net xnet

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The write of a `Ready` that is not a `-parallel` leader's** (`drain`'s `else if write || role !=
n.role { … }`, its condition evaluated to `b`; synchronous storage, no batching, no split write): from the
state right after the `Ready` (`drainPreB2`, `n.hs` at `hsl`; `hs` at `hp`, the `Ready`'s hard state if
it has one, else `hsl`, as `node.parallel.spec`'s), the report (`reportCause`, then `announce` and the
disk and storage written, or `emit` with nothing to write; nothing reported when `b` is false), then
either alive at the view `v₁` after it (`drainMidB2`, the write entered) with the `Ready`'s messages owned
and certified (`drainMsgsB1`) and pending in their order, or dead (killed on the way, or before it:
`nodeOwnB2HD … .drained none true`, as `node.parallel.spec`'s). -/
abbrev drainSyncB2.stmt : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (np bp rdp hsp wrp rlp c n : Loc) (γ : AntNamesB2) (j : Fin γ.R.N)
    (I : DrainIterB1) (x : CrashNames) (g : Nat) (net₀ : List Msg) (xnet₀ : List XMsg)
    (hsl hp : Loc) (wr b : Bool) (q : Qp) (Φ : val → IProp GF),
  γ.mode.Async' = false → γ.mode.Batch' = false → γ.mode.Split' = W64 0 →
  ¬ (γ.mode.Parallel' = true ∧ roleAfter I.rs.role I.ss = StateLeader) →
  (HsNew I.h → hp = I.rd.HardState') → (¬ HsNew I.h → hp = hsl) → (HsNew I.h → I.h ≠ I.rs.phs) →
  (wr = true ↔ HsNew I.h ∨ I.es ≠ []) →
  (b = true ↔ wr = true ∨ roleStr (roleAfter I.rs.role I.ss) ≠ AntSim.roleS I.v) →
  isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ ⌜DrainB2 γ.scope γ.mode⌝ ∗
      np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗ hsp ↦ hp ∗ wrp ↦ wr ∗
      rlp ↦ roleStr (roleAfter I.rs.role I.ss) ∗
      drainPreB2 γ j n I x g net₀ xnet₀ hsl ∗ nodeExitB2 c γ q ∗ threadTok ∗
      (∀ (v₁ : AntSim.NodeView) (net₁ : List Msg) (xnet₁ : List XMsg),
        np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗ hsp ↦ hp ∗ wrp ↦ wr ∗
          rlp ↦ roleStr (roleAfter I.rs.role I.ss) ∗ nodeExitB2 c γ q ∗ threadTok ∗
          ((drainMidB2 γ j n I v₁ net₁ xnet₁ ∗ drainMsgsB1 γ.toAntNames j I ∗
              ⌜v₁.pend = I.ms.filterMap (fun m => absMsgOf m.st) ∧
                v₁.xpend = I.ms.filterMap (fun m => xmsgOf m.st)⌝) ∨
            nodeOwnB2HD c γ j n v₁ .drained none true) -∗
          Φ executeVal) ⊢
    WP (If (Val #b) (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.drain.syncBodyE
        np bp rdp hsp wrp rlp) (App (Val doExecute) (Val #())))
      {{ Φ }}

end defs

end AntHarness
end EtcdGrove
end Perennial
