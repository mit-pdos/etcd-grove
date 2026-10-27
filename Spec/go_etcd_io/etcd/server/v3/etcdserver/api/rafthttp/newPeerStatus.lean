/-
`newPeerStatus(urls)` (`peer_status.go`; rafthttp stage 6b). Lean-first.
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

/-- **`newPeerStatus(lg, local, id)`** of a logger (not `nil`): a peer status. -/
abbrev rafthttp.newPeerStatus.spec : Prop :=
  ∀ (lg : Loc) (lid id : go_etcd_io.etcd.client.pkg.v3.types.ID),
  lg ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }}
    (App (App (App (Val (@! rafthttp.newPeerStatus)) (Val #lg)) (Val #lid)) (Val #id))
  {{ (s : Loc), RET #s; peerStatusOk s }}

end spec

end EtcdGrove
end Perennial
