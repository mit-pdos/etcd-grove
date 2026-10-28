/-
`(*peerStatus).deactivate` (`peer_status.go`; rafthttp stage 4d). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PeerStatus

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `s.deactivate(failure, reason)`: marks the peer inactive (logging and counting it if it was active). -/
abbrev rafthttp.peerStatus.deactivate.spec : Prop :=
  ∀ (s : Loc) (failure : rafthttp.failureType) (reason : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      peerStatusOk s }}
    (App (App (Val (s @!! go.GoType.PointerType rafthttp.peerStatus.ty @!! go!"deactivate")) (Val #failure)) (Val #reason))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
