/-
## `streamType.endpoint(lg)`

**Users.** `streamHandler.ServeHTTP`, `streamReader.dial`.

**Proof sketch.** `path.Join(RaftStreamPrefix, ...)` (Go's `path`, translated: clean segments join with one slash; `RaftStreamPrefix`'s initializer gives `/raft/stream`).

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

/-- (internal) The stream type's path prefix (`/raft/stream/msgapp`, `/raft/stream/message`). -/
def streamType.endpoint.spec : Prop :=
  ∀ (t : StreamTy) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) }}
    (App (Val (t.str @!! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamType.ty @!! go!"endpoint")) (Val #lg))
  {{ RET #(t.endpoint); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
