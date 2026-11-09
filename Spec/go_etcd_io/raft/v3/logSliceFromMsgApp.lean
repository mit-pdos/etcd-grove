/-
## `logSliceFromMsgApp(m)` (internal)

`handleAppendEntries`. Mirrors the code: the message's term, previous entry id and entries (the
message's slice: for a `MsgApp`, read-only entries from `Index + 1`, raftpb's `msgPts_unfold` and
`msgEnts_app`, which `raftLog.maybeAppend` takes). **Changes.** (Integration I2) the entries named
(R3's request, `req/go_etcd_io_raft_v3.md`, "from R3, round 1", item 5). **Margin.** No capacity of
the slice is given: raftpb's `msgPts` owns none (3h: a `MsgApp`'s slice is a sub-slice of the
leader's log, `limitSize`'s `ents[:limit]` keeping the leader's capacity), so `maybeAppend`'s
capacity premise cannot be met from here (`raft.handleAppendEntries`'s gap, recorded there).
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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
  ∀ (ml : Loc) (dq : DFrac) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ msgPts ml dq m }}
    (App (Val (@! go_etcd_io.raft.v3.logSliceFromMsgApp)) (Val #ml))
  {{ (ls : go_etcd_io.raft.v3.logSlice), RET #ls; msgPts ml dq m ∗
      ⌜ls.term' = m.term ∧ ls.prev'.term' = m.logTerm ∧ ls.prev'.index' = m.index⌝ ∗
      (⌜m.type = MsgApp⌝ -∗ entriesRO ls.entries' (uint.nat m.index + 1) m.entries) }}

end spec
end Raft
end EtcdGrove
end Perennial
