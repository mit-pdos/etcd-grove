-- The copy for the part `KvNet/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/quietLogger__Errorf.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`quietLogger{}.Errorf(format, args)` (cluster.go): discards what raft logs (one of the four methods
raft's `Logger` contract needs, `isLogger`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.QLogger

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- See the file header. -/
abbrev quietLogger.Errorf.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice),
  {{ (True : IProp GF) }}
    (App (App (Val (qLoggerV @!! qLoggerTy @!! go!"Errorf")) (Val #format)) (Val #args))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
