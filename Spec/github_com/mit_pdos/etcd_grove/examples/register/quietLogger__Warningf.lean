/- Lean-first (no Rocq counterpart).

`quietLogger.Warningf(format, v...)` (cluster.go): returns, logging nothing. With the other
formatting methods it makes `quietLogger{}` a raft `Logger` (`qLogger_isLogger`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

/-- See the file header. -/
abbrev quietLogger.Warningf.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice),
  {{ (True : IProp GF) }}
    (App (App (Val (qLoggerV @!! qLoggerTy @!! go!"Warningf")) (Val #format)) (Val #args))
  {{ RET #(); True }}

end spec

end register
end EtcdGrove
end Perennial
