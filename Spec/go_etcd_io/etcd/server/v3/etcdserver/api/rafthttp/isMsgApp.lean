/-
## `isMsgApp(m)`

**Users.** `peer.send`, `peer.pick`, `pipeline.handle`, `Transport.Send`.

**Proof sketch.** `GetType` (raftpb's getter, 3h).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

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

/-- (internal) Whether the message is a `MsgApp`. -/
def isMsgApp.spec : Prop :=
  ∀ (ml : Loc) (dq : DFrac) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ msgPts ml dq m }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isMsgApp)) (Val #ml))
  {{ RET #(decide (m.type = MsgApp)); msgPts ml dq m }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
