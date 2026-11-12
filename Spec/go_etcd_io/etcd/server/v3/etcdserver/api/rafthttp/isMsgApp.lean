/-
`isMsgApp` (`peer.go`; rafthttp stage 4d). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PbMessage

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

/-- `isMsgApp(m)`: whether `m` is a `MsgApp`. -/
abbrev rafthttp.isMsgApp.spec : Prop :=
  ∀ (ml : Loc) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      msgOwn ml DFrac.discard st }}
    (App (Val (@! rafthttp.isMsgApp)) (Val #ml))
  {{ RET #(decide (st.msg.Type' = MsgApp)); True }}

end spec

end EtcdGrove
end Perennial
