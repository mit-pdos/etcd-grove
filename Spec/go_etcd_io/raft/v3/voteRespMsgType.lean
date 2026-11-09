/-
## `voteRespMsgType(msgt)` (internal)

**Users**: vote handling (`raft.go:1077,1270,1279`), on a `MsgVote`/`MsgPreVote`. Panics on any
other type (the premise). **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/voteRespMsgType.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) The response type of a vote or pre-vote. -/
def voteRespMsgType.spec : Prop :=
  ∀ (t : w32),
  t = MsgVote ∨ t = MsgPreVote →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val (@! go_etcd_io.raft.v3.voteRespMsgType)) (Val #t))
  {{ RET #(if t = MsgVote then MsgVoteResp else MsgPreVoteResp); True }}

end spec
end Raft
end EtcdGrove
end Perennial
