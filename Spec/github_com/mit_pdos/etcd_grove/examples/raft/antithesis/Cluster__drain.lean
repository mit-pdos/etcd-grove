/-
Lean-first (no Rocq counterpart). #33 S4, specs first, part 2 (`notes/antithesis-s4-design.md` §2-§3;
the vocabulary is `HarnessInv.lean`'s).
`(*Cluster).drain(n, by)`: from the loop head (`nodeOwn … (.loop net₀ ps₁)`: the node reached
from its view by an input, or by nothing at the boot drain), each `Ready` until `HasReady` is
false: the `ready` report if the write or the role changed (`antSim_ready`, or `antSim_quiet`'s
silent `Ready`), the write, each message's `send` report and hand-over (`antSim_send`, `send`), the
committed entries' `apply` report (`antSim_apply`), `Advance` (the next loop head: `Reach.advance`);
the drain's `recv` reported before its first report (`reportCause`). The node ends drained, idle
(`PIdle`), its view at its state (`antSim_quiet`'s `noReady`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInv

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
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. The view's `byE` is kept (2026-11-24: `Cluster.run`'s tick and proposal drains
need the cause cell to stay nil). -/
abbrev Cluster.drain.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNames) (n : Loc) (j : Fin 3)
    (v : AntSim.NodeView) (net₀ : List Msg) (ps₁ : PState) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO γ n j ∗ nodeOwn c γ j n v (.loop net₀ ps₁) ∗ netAdder c γ q ∗
      threadTok }}
    (App (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"drain")) (Val #n)) (Val #v.byE))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwn c γ j n v' .drained ∗ netAdder c γ q ∗ threadTok ∗
      ⌜v'.byE = v.byE⌝ }}

end spec

end AntHarness
end EtcdGrove
end Perennial
