/-
`isLinkHeartbeatMessage(m)` (`stream.go`): whether a message is the streams' link heartbeat.
Lean-first; the model: `rafthttp/MsgAppV2.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.MsgAppV2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `isLinkHeartbeatMessage(m)` of a message: whether it is a `MsgHeartbeat` from and to `0`. -/
abbrev rafthttp.isLinkHeartbeatMessage.spec : Prop :=
  ∀ (ml : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      msgPtsC ml dq dqe cap st }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isLinkHeartbeatMessage))
      (Val #ml))
  {{ RET #(decide (isHB st.msg)); msgPtsC ml dq dqe cap st }}

end spec

end EtcdGrove
end Perennial
