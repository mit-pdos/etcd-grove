/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `durableOf(v)`: the record `PersistState` writes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `durableOf(v)`, of a `*Server` read at any fraction (a shared server, or a copy being
written, `persistState`'s): the record `durableOf v` of the fields it reads. -/
abbrev durableOf.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (g : G.Server) (v : Server),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      p ↦{dq} g ∗
      ⌜sint.Z g.CurrentTerm' = v.currentTerm ∧ uint.nat g.VotedFor' = v.votedFor ∧
        sint.Z g.CommitIndex' = v.commitIndex⌝ ∗
      logRO g.Log' v.log ∗ configRO g.Config' v.config }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.durableOf)) (Val #p))
  {{ (d : G.Durable), RET #d; p ↦{dq} g ∗ durableRO d (durableOf v) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
