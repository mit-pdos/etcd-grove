/-
## `(*peerStatus).activeSince()`

**Users.** `peer.activeSince`.

**Proof sketch.** Under `mu`.

**Changes.** New (no old spec).

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

/-- (internal) Since when the peer is active (zero if not). -/
def peerStatus.activeSince.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ statusAt s }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus.ty @!! go!"activeSince")) (Val #()))
  {{ (tm : _root_.Perennial.time.Time), RET #tm; True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
