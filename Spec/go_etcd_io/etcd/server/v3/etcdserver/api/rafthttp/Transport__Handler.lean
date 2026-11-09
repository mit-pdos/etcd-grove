/-
## `(*Transport).Handler()`

**Users.** etcd's `EtcdServer.RaftHandler` (`server.go:646`), registered by `etcdhttp.NewPeerHandler` at `/raft` and `/raft/` (`etcdserver/api/etcdhttp/peer.go:64-65`) on the peer listener `embed` serves. Snippet: `receive.go` (`ReqServePeer`).

**Proof sketch.** `newPipelineHandler`, `newStreamHandler`, `newSnapshotHandler` (each `phAt`/`sthAt`/`shAt` from `isTransport`'s `Raft` and snapshotter), `probing.NewHandler` (trust: a handler answering any request, which `raftProto` allows), `NewServeMux` and four `Handle`s (`Http.muxOwn`); `Http.mux_handlerOk.spec` with the handlers' contracts (their `ServeHTTP` specs) and `raftProto_muxAnswers.spec` for the unrouted paths.

**Changes.** Restated: was `RaftHandler`'s `raftHandlerOf` over the network contract; now the HTTP boundary's handler contract, at the root, for every protocol compatible with rafthttp's (round 1: the handler is served at the root by the examples, beside other handlers by etcd's peer mux; `Http.handlerOk_narrow` gives a narrower pattern). The proof: `handlerOk h (raftProto ν) "/"` from the mux, then `Http.handlerOk_agree` with each pattern's agreement, the mux's own answers allowed by `raftCompat`.

**Margin.** Says only what the HTTP boundary sees; what a delivery gives the receiver is `raftOk`'s `Process` premise.
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

/-- **The transport's HTTP handler**: a `ServeMux` serving rafthttp's protocol on `/raft` and its subtree (the pipeline at `/raft`, the streams under `/raft/stream/`, snapshots at `/raft/snapshot`, the probe at `/raft/probing`; the mux's `404`/`301` elsewhere). -/
def Transport.Handler.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"Handler")) (Val #()))
  {{ (h : GoInterface), RET #h; □ ∀ P : Http.Proto GF, ⌜raftCompat ν P⌝ → Http.handlerOk h P go!"/" }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
