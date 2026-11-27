/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 4: nothing proves
`node.parallel.spec` yet; the vocabulary is `DrainB2Phases.lean`'s).
`(*node).parallel(by, role, hs, rd)`: a leader's synchronous `Ready` with `Mode.Parallel`, up to its
write: the `mem` report (if it writes or the role changed), the requests (appends and heartbeats)
reported and sent, then the write (`write`, `saveDisk`, where the `Ready`'s enter promise fires,
`wrote`, the storage); with nothing to write, the enter promise fires after the reports. The node ends
at the iteration's state after the write (`drainMidB2`) with the other messages pending, or killed on
the way (dead: `drain` returns).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Phases

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. `hp` is `drain`'s `hs`: the `Ready`'s hard state if it has one, else `n.hs`
(`hsl`). -/
abbrev node.parallel.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (I : DrainIterB1) (x : CrashNames) (g : Nat) (net₀ : List Msg) (xnet₀ : List XMsg) (hsl hp : Loc)
    (q : Qp),
  γ.mode.Async' = false → γ.mode.Batch' = false → γ.mode.Parallel' = true →
  roleAfter I.rs.role I.ss = StateLeader →
  (HsNew I.h → hp = I.rd.HardState') → (¬ HsNew I.h → hp = hsl) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ ⌜DrainB2 γ.scope γ.mode⌝ ∗
      drainPreB2 γ j n I x g net₀ xnet₀ hsl ∗ netAdder c γ.toAntNames q ∗ threadTok }}
    (App (App (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"parallel"))
      (Val #I.v.byE)) (Val #(roleStr (roleAfter I.rs.role I.ss)))) (Val #hp)) (Val #I.rd))
  {{ (v₁ : AntSim.NodeView) (net₁ : List Msg) (xnet₁ : List XMsg), RET #();
      ((drainMidB2 γ j n I v₁ net₁ xnet₁ ∗ drainMsgsParB2 γ j I ∗
        ⌜v₁.pend = (I.ms.filter (fun m => !isRequestTy m.st.msg.Type')).filterMap (fun m => absMsgOf m.st) ∧
          v₁.xpend = I.ms.filterMap (fun m => xmsgOf m.st)⌝) ∨
       nodeOwnB2HD c γ j n v₁ .drained none true) ∗
      netAdder c γ.toAntNames q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
