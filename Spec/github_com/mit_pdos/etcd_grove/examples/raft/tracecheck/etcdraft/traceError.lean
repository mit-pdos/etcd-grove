/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `traceError(what, line, n)`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceRead

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

/-- `traceError(what, line, n)`: an error (not nil; `NewTrace`'s callers test only that). -/
abbrev traceError.spec : Prop :=
  ∀ (what : GoString) (line n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.traceError))
      (Val #what)) (Val #line)) (Val #n))
  {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
