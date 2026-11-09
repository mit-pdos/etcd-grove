/-
## `traceReplicate(...)` (internal)

raft.go's tracing hook: a no-op in the default build (`state_trace_nop.go`; the translated one).
**Changes.** Unchanged (from `specs-ref`'s `traceReplicate.lean`).
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

/-- (internal) Does nothing. -/
def traceReplicate.spec : Prop :=
  ∀ (r : Loc) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (App (Val (@! go_etcd_io.raft.v3.traceReplicate)) (Val #r)) (Val #sl))
  {{ RET #(); True }}

end spec
end Raft
end EtcdGrove
end Perennial
