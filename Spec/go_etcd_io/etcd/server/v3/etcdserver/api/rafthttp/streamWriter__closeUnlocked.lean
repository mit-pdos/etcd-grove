/-
## `(*streamWriter).closeUnlocked()`

**Users.** `streamWriter.close`, `run`.

**Proof sketch.** The connection's close right (`closer.Close`), `ReportUnreachable` if messages are queued, a new channel (the old one's messages lost with their facts).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Under the lock: closes a working connection (giving the handler its writer back), drops the queue (a fresh `msgc`), stops working. -/
def streamWriter.closeUnlocked.spec : Prop :=
  ∀ (cw : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ swLocked cw ∗ swRun cw }}
    (App (Val (cw @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter.ty @!! go!"closeUnlocked")) (Val #()))
  {{ (b : Bool), RET #b; swLocked cw ∗ swRun cw }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
