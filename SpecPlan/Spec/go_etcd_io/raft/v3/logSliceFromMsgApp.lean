/-
## `logSliceFromMsgApp(m)` (internal)

`handleAppendEntries`. Mirrors the code: the message's term, previous entry id and entries (the
message's slice: for a `MsgApp`, read-only entries from `Index + 1`, raftpb's `msgPts_unfold` and
`msgEnts_app`, which `raftLog.maybeAppend` takes). **Changes.** (Integration I2) the entries named
(R3's request, `req/go_etcd_io_raft_v3.md`, "from R3, round 1", item 5); from a received message
(`rc`: `msgRecv`, the coordinator's decision) the slice's capacity too, split off the message (which
stays `msgPts` at `own 1`), for `maybeAppend`, whose `unstable` may adopt the slice. **Margin.** From
a `msgPts` alone no capacity is given (`msgPts` is shared read-only; a `MsgApp` raft builds has
none to give: `raftLog.slice` clips, log.go:510).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) The appended slice an `MsgApp` describes. -/
def logSliceFromMsgApp.spec : Prop :=
  ∀ (ml : Loc) (dq : DFrac) (m : Msg) (rc : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      (if rc then msgRecv ml m else msgPts ml dq m) }}
    (App (Val (@! go_etcd_io.raft.v3.logSliceFromMsgApp)) (Val #ml))
  {{ (ls : go_etcd_io.raft.v3.logSlice), RET #ls; msgPts ml (if rc then DFrac.own 1 else dq) m ∗
      (if rc then ownSliceCap Loc ls.entries' (DFrac.own 1) else iprop(True)) ∗
      ⌜ls.term' = m.term ∧ ls.prev'.term' = m.logTerm ∧ ls.prev'.index' = m.index⌝ ∗
      (⌜m.type = MsgApp⌝ -∗ entriesRO ls.entries' (uint.nat m.index + 1) m.entries) }}

end spec
end Raft
end EtcdGrove
end Perennial
