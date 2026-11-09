/-
## `(*readOnly).maybeAdvance(c)` (internal)

**Users**: `stepLeader`'s `MsgHeartbeatResp` (`raft.go:1620`, with `r.trk.Voters`). Snippet
`raftlog/readindex.go` (`ReqReadIndexQuorum`).

**Proof sketch**: `c.CommittedIndex(ro)` (R4's spec with `ro` as an `AckedIndexer`:
`readOnly.AckedIndex.spec`) gives `N` with `JointIdx`. The reslices are in bounds: `N` is at most
some voter's acknowledgement (a non-empty half's quorum index is one of its voters' values), at most
the position (premise). The returned prefix aliases the queue's array; it is handed out read-only
for good (nothing writes a request again).

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/readOnly__maybeAdvance.lean`: the halves through R4's
`Quorum.jointConfigOwn` (was `ownIdsetQ` of `c.arr`'s maps). (Integration I2: the size premise in
R4's form, `GMap.size … ≤ Quorum.sortMax`, as `JointConfig.CommittedIndex.spec` takes it; `ro` meets
`Quorum.isAckedIndexer (ro as an AckedIndexer) (readOnly ro rs) (rs.acks !! ·)` by
`readOnly.AckedIndex.spec`, so the result's `JointIdx … ((rs.acks !! ·).getD 0)` is `rs.ackOf`'s.)

**Margin**: none. The size bound is quorum's `CommittedIndex`'s (its sort), kept here, local.
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

/-- (internal) Confirm the requests a quorum of voters acknowledged, returning them. -/
def readOnly.maybeAdvance.spec : Prop :=
  ∀ (ro : Loc) (rs : ReadOnlyState) (c : go_etcd_io.raft.v3.quorum.JointConfig) (dq : DFrac)
    (s0 s1 : GSet w64),
  GMap.size s0 ≤ Quorum.sortMax → GMap.size s1 ≤ Quorum.sortMax →
  s0 ∪ s1 ≠ ∅ →
  (∀ v, v ∈ s0 ∪ s1 → uint.nat (rs.ackOf v) ≤ rs.position) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ readOnly ro rs ∗ jointConfigOwn c dq s0 s1 }}
    (App (Val (ro @!! go.GoType.PointerType go_etcd_io.raft.v3.readOnly.ty @!! go!"maybeAdvance")) (Val #c))
  {{ (sl : GoSlice), RET #sl; ∃ N : w64, ⌜JointIdx s0 s1 rs.ackOf N⌝ ∗
      readOnly ro (rs.advance N).1 ∗ readReqsRO sl (rs.advance N).2 ∗
      jointConfigOwn c dq s0 s1 }}

end spec
end Raft
end EtcdGrove
end Perennial
