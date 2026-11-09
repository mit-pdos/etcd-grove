/-
## `(*Transport).Stop()`

**Users.** etcd's `raftNode.onStop` (`raft.go:440`). Snippet: `transport.go` (`ReqStop`).

**Proof sketch.** `Lock`; each remote's and peer's stop right (`remote.stop`, `peer.stop`), the probes' `RemoveAll` (trust), the round trippers' `CloseIdleConnections` when they are `*http.Transport`s (a type assertion; the boundary's spec), the maps set to `nil` (with `trRunning t 1` the invariant may drop "maps non-nil"); `Unlock`.

**Changes.** New (the old tree had no spec of `Stop`; the server's stop path was outside the proved scope).

**Margin.** Says nothing of quiescence: a peer's two `Process` loops and the HTTP handlers may still be running (they end on their own); `Process` calls may still arrive.
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

/-- **Stops the transport**: every peer's and remote's goroutines stopped (the writers, readers and pipeline workers joined); later calls are no-ops but `AddPeer`, which the spent token forbids. -/
def Transport.Stop.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ trRunning t 1 }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
