/-
`(*peerStatus).activeSince` (`peer_status.go`; rdslot, 2026-11-22). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PeerStatus

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`s.activeSince()`**: the time the peer became active (the zero time if it is not), read
under the status's mutex. -/
abbrev rafthttp.peerStatus.activeSince.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      peerStatusOk s }}
    (App (Val (s @!! go.GoType.PointerType rafthttp.peerStatus.ty @!! go!"activeSince")) (Val #()))
  {{ (t : _root_.Perennial.time.Time), RET #t; True }}

end spec

end EtcdGrove
end Perennial
