/- Lean-first (no Rocq counterpart).

`quietLogger{}.Infof(format, args)` (cluster.go): discards what raft logs (one of the four methods
raft's `Logger` contract needs, `isLogger`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.QLogger

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

/-- See the file header. -/
abbrev quietLogger.Infof.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice),
  {{ (True : IProp GF) }}
    (App (App (Val (qLoggerV @!! qLoggerTy @!! go!"Infof")) (Val #format)) (Val #args))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
