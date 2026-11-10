/- Lean-first (no Rocq counterpart). -/
module

public import Proof.go_etcd_io.raft.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `SetLogger(l)` (`logger.go`): installs `l` as raft's package logger, `raftLogger`, under
`raftLoggerMu`. It returns, for any `l`; the package's initialization owns the two globals (the
mutex and the variable it guards, `isInitialized`). (premise-fixes-4, 2026-11-10: until then the
server took this triple as the premise `rnSetLoggerOk`, which was false in the model.) -/
abbrev SetLogger.spec : Prop :=
  ∀ (l : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions SetLogger [])) (Val #l))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
