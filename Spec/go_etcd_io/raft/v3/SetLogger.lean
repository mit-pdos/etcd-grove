/-
## `SetLogger(l)`

**Users.** etcd's `newRaftNode` (`server/etcdserver/raft.go`: `raft.SetLogger` with the zap adapter,
which meets `loggerOk`: the zap batch's law); tests. R1's request 6. Snippet: `status.go`
(`ReqLogger`).

**Proof sketch.** Under `raftLoggerMu`, whose lock invariant (in the package's initialization,
`isPkgInit`) holds `raftLogger` with `loggerOk`. **Changes** (from `specs-ref`'s logger axioms): a
spec of the code. **Margin.** None.
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

/-- Sets the package's logger (one meeting `loggerOk`). -/
def SetLogger.spec : Prop :=
  ∀ (l : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ loggerOk l }}
    (App (Val (@! go_etcd_io.raft.v3.SetLogger)) (Val #l))
  {{ RET #(); True }}

end spec
end Raft
end EtcdGrove
end Perennial
