/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08, `notes/trace-validation-plan.md`,
"Probe set"): `Server.copy()`: a fresh copy of a server, its `MatchIndex` map copied.
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

/-- `v.copy()`: an owned copy holding the same server. -/
abbrev Server.copy.spec : Prop :=
  ∀ (p : Loc) (v : Server),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      serverRO p v }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Server.ty
      @!! go!"copy")) (Val #()))
  {{ (q : Loc), RET #q; serverOwn q v }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
