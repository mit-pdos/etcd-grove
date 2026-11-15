/-
## `(*Transport).ActiveSince(id)`

**Users.** etcd's `mayRemoveMember` (`server.go:1655`), `isConnectedSince`/`longestConnected` (`server/etcdserver/util.go:53,92`): health heuristics for member removal, leader transfer and promotion. Snippet: `transport.go` (`ReqConnected`).

**Proof sketch.** `RLock` with the token; the peer's `activeSince` (`peerStatus` under its mutex); `RUnlock`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** The value is not related to any connection fact: the callers use it only for heuristics that refuse an operation or pick a target.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

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

/-- **When the connection with peer `id` became active** (zero if inactive or unknown): some time. -/
def Transport.ActiveSince.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ threadTok }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"ActiveSince")) (Val #pid))
  {{ (tm : _root_.Perennial.time.Time), RET #tm; threadTok }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
