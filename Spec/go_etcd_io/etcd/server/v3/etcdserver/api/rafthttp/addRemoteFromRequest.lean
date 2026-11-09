/-
## `addRemoteFromRequest(tr, r)`

**Users.** `pipelineHandler.ServeHTTP`, `snapshotHandler.ServeHTTP`.

**Proof sketch.** `Header.Get`, `types.IDFromString`, `strings.Split`, `Transport.AddRemote` (its premises from `raftProto`'s request knowledge: the sender's `X-PeerURLs` are its `URLs`, `trCfg`'s peer addresses).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. (`nonissues/etcd-rafthttp-addremote-bad-peerurls-panic.md`: a non-member's malformed header is outside the closed world.)

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

/-- (internal) Adds the sender as a remote from `X-Server-From` and `X-PeerURLs` (a member's request: the URLs parse and are peer addresses). -/
def addRemoteFromRequest.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid : w64) (r : Loc) (R : Http.HReq) (rd : GoInterface) (τ : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ Http.srvReq r R rd ∗ □ (raftProto ν).hreq R τ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.addRemoteFromRequest)) (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t))) (Val #r))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
