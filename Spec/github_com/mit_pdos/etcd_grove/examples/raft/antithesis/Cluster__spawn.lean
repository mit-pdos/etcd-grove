/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*Cluster).spawn(f)`: `behWg.Add(1)`, then `f` on a goroutine of its own (a fresh thread token,
given back at its end), which then calls `behWg.Done()`. `f` is a function value (`#f` for
`f : GoFunc`, so `spawn`'s call and its `GoAlloc` of `f` step), and its call must end normally
(`⌜v = #()⌝`): the fork rule takes no goroutine that panics.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun

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

/-- See the file header. -/
abbrev Cluster.spawn.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (f : GoFunc) (k : w32) (P : IProp GF), sint.Z k < 2 ^ 31 - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      sync.join.ownAdder (c.[H.Cluster, go!"behWg"]) k P ∗ threadTok ∗
      (threadTok -∗ WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ ∗ threadTok }}) }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"spawn")) (Val #f))
  {{ RET #(); sync.join.ownAdder (c.[H.Cluster, go!"behWg"]) (k + W32 1) iprop(P ∗ True) ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
