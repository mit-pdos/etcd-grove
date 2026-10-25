/-
`(*peer).attachOutgoingConn` (`peer.go`; rafthttp stage 5e-2). Lean-first; the peer:
`rafthttp/Peer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Peer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`p.attachOutgoingConn(conn)`** of a connection of type `ty` from `lid` to `pid`: hands it to
the peer's stream writer of that type, or closes it (giving its writer back to its handler). -/
abbrev rafthttp.peer.attachOutgoingConn.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (p conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      peerStreams Rh lid pid p ∗ outConnOk Rh ty lid pid conn }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.peer.ty @!! go!"attachOutgoingConn"))
      (Val #conn))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
