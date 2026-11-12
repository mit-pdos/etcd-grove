/-
`v3rpc.IsCreateEvent` (`watch.go`). Lean-first (no Rocq counterpart); the
vocabulary is `v3rpc/InvWatchStream.lean` and `v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`IsCreateEvent(e)`** of an mvcc event `ev`: a put whose key-value was created at its
modification (`CreateRevision == ModRevision`). -/
abbrev v3rpc.IsCreateEvent.spec : Prop :=
  ∀ (e : Loc) (ev : mvcc.EvM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ mvcc.evIs e ev }}
    (App (Val (@! v3rpc.IsCreateEvent)) (Val #e))
  {{ (b : Bool), RET #b; ⌜b = (!ev.del && decide (ev.kv.createRev = ev.kv.modRev))⌝ }}

end spec

end EtcdGrove
end Perennial
