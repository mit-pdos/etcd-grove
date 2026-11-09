/-
## `(*readOnly).recvAck(from, ctx)` (internal)

**Users**: `stepLeader`'s `MsgHeartbeatResp` (`raft.go:1619`, the context the follower echoed), the
leader's own ack (`raft.go:2164`, its `heartbeatCtx`). **Proof sketch**: `binary.LittleEndian.Uint64`
reads 8 bytes: a non-empty context shorter than 8 panics (the premise: the leader's contexts are
`heartbeatCtx`'s, a follower echoes them). **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/readOnly__recvAck.lean`.
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

/-- (internal) Record `from`'s acknowledgement of position `ctx` (if any). -/
def readOnly.recvAck.spec : Prop :=
  ∀ (ro : Loc) (rs : ReadOnlyState) (src : w64) (ctx : GoSlice) (cs : List w8) (dq : DFrac),
  (cs = [] ∨ 8 ≤ cs.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ readOnly ro rs ∗ ctx ↦*{dq} cs }}
    (App (App (Val (ro @!! go.GoType.PointerType go_etcd_io.raft.v3.readOnly.ty @!! go!"recvAck")) (Val #src)) (Val #ctx))
  {{ RET #(); readOnly ro (rs.recvAck src cs) ∗ ctx ↦*{dq} cs }}

end spec
end Raft
end EtcdGrove
end Perennial
