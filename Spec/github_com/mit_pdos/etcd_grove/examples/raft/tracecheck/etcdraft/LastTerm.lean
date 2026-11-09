/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `LastTerm(xlog)` (`lastTerm`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

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

/-- `LastTerm(xlog)`: the last entry's term, 0 for the empty log. -/
abbrev LastTerm.spec : Prop :=
  ∀ (sl : GoSlice) (l : List Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      logRO sl l }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.LastTerm)) (Val #sl))
  {{ (t : w64), RET #t; ⌜sint.Z t = lastTerm l⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
