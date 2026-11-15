/-
## `(*streamHandler).ServeHTTP(w, r)`

**Users.** `Transport.Handler`'s mux at `/raft/stream/`.

**Proof sketch.** The method; `X-Server-Version` and the cluster id set on the header map (`Http.respW_header.spec`, `Header.Set`: the response headers `raftProto` asks); the compatibility check; `path.Dir` against the two `endpoint`s, `path.Base`, `types.IDFromString` (the requester `B`); `IsIDRemoved(B)` (`raftOk`, the token): `410`; `Transport.Get(B)`: none: `AddRemote` from `X-PeerURLs`, `404`; `X-Raft-To` not the local id: `412`. Then `WriteHeader(200)`, `Flush`, `newCloseNotifier`, the `outgoingConn` (the writer, committed, as `outConn` for `B`'s reader tokens named by `τ` in the registry: `raftProto`'s request knowledge), `attachOutgoingConn`, and a receive on the close notifier, which gives the writer back (`serveDone`). A replayed `GET` (no ticket) only opens a connection whose bytes no client reads. `types.ID`'s `String()` on an addressable `ID` (log fields, headers) is 1c's `Types.ID.String_ptr.spec` (Goose's pointer receiver).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (second pass): the sketch cites `Types.ID.String_ptr.spec`.

**Margin.** None.
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

/-- (internal) **Serves a stream GET**: checks it, answers `200`, hands the response writer to the peer's writer of the stream's type and waits until that writer closes it; or refuses (`405`, `412`, `404`, `410`). -/
def streamHandler.ServeHTTP.spec : Prop :=
  ∀ (hp : Loc) (ν : Net GF) (lid : w64) (w : GoInterface) (r : Loc) (R : Http.HReq) (τ : GName) (rd : GoInterface),
  ⊢ (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ sthAt hp ν lid ∗ Http.servePre (raftProto ν) go!"/raft/stream/" w r R τ rd) -∗
    WP (App (App (Val (hp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamHandler.ty @!! go!"ServeHTTP")) (Val #w)) (Val #r))
    {{ v, Http.serveDone (raftProto ν) w R τ v }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
