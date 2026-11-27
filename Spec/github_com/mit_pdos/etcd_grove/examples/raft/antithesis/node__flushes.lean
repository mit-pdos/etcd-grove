/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves `node.flushes.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`(*node).flushes(k)`: `k` `flush` reports (`more` from the second on), each by `emit`: if the node
dies on the way (its fuse), the rest is not recorded (`reportsOrDead`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDur

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

/-- See the file header. -/
abbrev node.flushes.spec : Prop :=
  ∀ (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (k : w64) (dead : Bool) (fuse : w64)
    (Q : IProp GF), 0 ≤ sint.Z k →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ killOwn n dead fuse ∗
      reports γ.strm ((flushEvs (sint.nat k)).map (atNode (AntSim.nameOf (AntSim.nodeId j)))) Q }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"flushes")) (Val #k))
  {{ (dead' : Bool) (fuse' : w64), RET #(); killOwn n dead' fuse' ∗ ⌜dead = true → dead' = true⌝ ∗
      reportsOrDead γ.strm dead' ((flushEvs (sint.nat k)).map (atNode (AntSim.nameOf (AntSim.nodeId j)))) Q }}

end spec

end AntHarness
end EtcdGrove
end Perennial
