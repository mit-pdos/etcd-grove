/- Lean-first (no Rocq counterpart).

# `raft/tracecheck`: its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): `raft_tracecheck_robust`
(`RaftTla/Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/TopLevelRobustness.lean`) has
premises that hold together with `Robust`'s antecedents (one fresh machine, its extension `idIssueExt`
in any state). It has no premise of its own (2026-11-28: the Iris premise `Hprem`, `proto.Marshal`'s
contract at the bootstrap log's conf changes, is now the trust-boundary axiom
`proto.MarshalBootConfChange.wp_proof`; the bootstrap log's pure facts, a premise until 2026-11-24, are
proved, `tracecheck.bootLogFacts_bootLog`). Checked by `etc/premise-witness.py`.
-/
module

public import RaftTla.Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

open Robustness

theorem raft_tracecheck_robust.premisesSat : premise_sat% raft_tracecheck_robust.spec := by
  intros
  exact ⟨freshState ((∅ : IdIssueState), ()), ⟨((), ()), ∅⟩,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

end EtcdGrove
end Perennial

end
