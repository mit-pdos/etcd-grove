/-
`(*peerStatus).isActive` (`stream.go`; rafthttp stage 5b). Lean-first; the reader's predicates:
`rafthttp/Reader.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PeerStatus

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`s.isActive()`**: whether the peer is active. -/
abbrev rafthttp.peerStatus.isActive.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      peerStatusOk s }}
    (App (Val (s @!! go.GoType.PointerType rafthttp.peerStatus.ty @!! go!"isActive")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
