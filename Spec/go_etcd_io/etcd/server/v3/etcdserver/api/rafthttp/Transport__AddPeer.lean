/-
## `(*Transport).AddPeer(id, us)`

**Users.** etcd's `NewServer` (`server.go:436`, the cluster's members), `applySnapshot` (`server.go:1166`, after `RemoveAllPeers`), `applyConfChange` (`server.go:2075`, an added member). Snippet: `transport.go` (`ReqStartTransport`, `ReqMembership`).

**Proof sketch.** `Lock`; stopped (`peers` nil): impossible by `trRunning`; known: return. `types.NewURLs` (1c: `urlsHosts`) succeeds; `LeaderStats.Follower` (2e), `startPeer` (`peerAt`, its stop right into the map invariant), two `addPeerToProber` (trust: the probes only measure), log; `Unlock`.

**Changes.** Restated over `peerAddr` (was `trURLsOk`/the network directory `γn.dir`: the URLs had to be the member's own; delivery to another member is now harmless, `Process` checks `To`).

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

/-- **`AddPeer(id, us)`** with URLs `NewURLs` accepts (it panics otherwise: the documented caller's responsibility), each host a peer address of `ν` and the transport not stopped (`AddPeer` after `Stop` panics: "transport stopped"). -/
def Transport.AddPeer.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid pid : w64) (sl : GoSlice) (us hs : List GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ trRunning t q ∗ sl ↦*{DFrac.discard} us ∗ ⌜urlsHosts us = some hs⌝ ∗ ⌜hs ≠ []⌝ ∗ ([∗list] a ∈ hs, peerAddr ν a) }}
    (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"AddPeer")) (Val #pid)) (Val #sl))
  {{ RET #(); trRunning t q }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
