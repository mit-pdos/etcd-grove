/-
## `(*Transport).UpdatePeer(id, us)`

**Users.** etcd's `applyConfChange` (`server.go:2101`, `ConfChangeUpdateNode`). Snippet: `transport.go` (`ReqMembership`).

**Proof sketch.** `Lock`; an unknown id: return. `NewURLs`; `peer.update` (the picker's URLs replaced: each host a peer address); the probes re-added; `Unlock`. `types.ID`'s `String()` on an addressable `ID` (log fields, headers) is 1c's `Types.ID.String_ptr.spec` (Goose's pointer receiver).

**Changes.** Restated over `peerAddr` (was `trURLsOk`/the network directory `γn.dir`: the URLs had to be the member's own; delivery to another member is now harmless, `Process` checks `To`). verify-round (second pass): the sketch cites `Types.ID.String_ptr.spec`.

**Margin.** The peer set is not tracked in the statement (no client needs it).
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

/-- **`UpdatePeer(id, us)`** with URLs `NewURLs` accepts (it panics otherwise: the documented caller's responsibility), each host a peer address of `ν` (a no-op for an unknown id). -/
def Transport.UpdatePeer.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid pid : w64) (sl : GoSlice) (us hs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ sl ↦*{DFrac.discard} us ∗ ⌜Types.urlsHosts us = some hs⌝ ∗ ⌜hs ≠ []⌝ ∗ ([∗list] a ∈ hs, peerAddr ν a) }}
    (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"UpdatePeer")) (Val #pid)) (Val #sl))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
