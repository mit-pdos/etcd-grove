/-
## `ResetDefaultLogger()`

**Users.** Tests only. **Proof sketch.** `SetLogger(defaultLogger)`: the default `*DefaultLogger`
meets `loggerOk` (the package's initialization). **Changes.** New. **Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Restores the default logger. -/
def ResetDefaultLogger.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val (@! go_etcd_io.raft.v3.ResetDefaultLogger)) (Val #()))
  {{ RET #(); True }}

end spec
end Raft
end EtcdGrove
end Perennial
