/-
`(*peer).send(m)` (`peer.go`; rafthttp stage 6b). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport

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

/-- **`p.send(m)`** of a started peer and a message for it (`peerMsg`): it returns, the message
handed to a stream writer or the pipeline, or dropped (paused, or the channel full: reported
unreachable). -/
abbrev rafthttp.peer.send.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (R : IProp GF) (p ml : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      peerOk Rh lid pid γd R p ∗ peerMsg Rh lid pid ml }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.peer.ty @!! go!"send")) (Val #ml))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
