/-
## `(*Transport).AddRemote(id, us)`

**Users.** etcd's `NewServer` (`server.go:431`, the remotes of a joining member); rafthttp's `addRemoteFromRequest` and `streamHandler` (requests from unknown members). Snippet: `transport.go` (`ReqStartTransport`).

**Proof sketch.** `Lock`; `remotes` nil (stopped), a known peer or remote: return. `NewURLs` succeeds; `startRemote` (`remoteAt`, its stop right into the map invariant); `Unlock`.

**Changes.** Restated over `peerAddr` (was `trURLsOk`/the network directory `γn.dir`: the URLs had to be the member's own; delivery to another member is now harmless, `Process` checks `To`). The remote-id list `L` and the four `R`s of a remote's pipeline are gone (thread tokens come from `Fork`).

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

/-- **`AddRemote(id, us)`** with URLs `NewURLs` accepts (it panics otherwise: the documented caller's responsibility), each host a peer address of `ν` (a no-op after `Stop`, or for a known peer or remote). -/
def Transport.AddRemote.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid pid : w64) (sl : GoSlice) (us hs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ sl ↦*{DFrac.discard} us ∗ ⌜urlsHosts us = some hs⌝ ∗ ⌜hs ≠ []⌝ ∗ ([∗list] a ∈ hs, peerAddr ν a) }}
    (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"AddRemote")) (Val #pid)) (Val #sl))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
