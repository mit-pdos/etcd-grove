/-
`watcherGroup.chooseAll` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchBatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchBatch
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchCmpSend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `wg.chooseAll(curRev, compactRev)`: of members each at or below `curRev` or restoring (it
excludes the `panic`; D22 receiver epochs, S6: the restore flag of each member above `curRev`
cleared, `chooseRst`), and (watches across a compaction, 2026-11-01) each with a `minRev` of at
least `0`, every member below `compactRev` is sent the compaction response
`WatchResponse{WatchID, CompactRevision: compactRev}` on its channel without blocking
(`cmpSendPre`: its channel's invariant and liveness, given back): on a send it is marked compacted
and deleted from the group (the members `Cm`, `chooseCmp`), on a full channel it stays (retried by
the next sync). The result is the least `minRev` of the members not behind `compactRev`
(`notBehind`), `math.MaxInt64` if none. Until 2026-11-01 every member was at or above
`compactRev` (the store never compacted). -/
abbrev mvcc.watcherGroup.chooseAll.spec : Prop :=
  ∀ (γ : mvcc.WsNames) (ql : Qp) (wg : Loc) (W : GMap Loc mvcc.WatchRange)
    (ST : GMap Loc mvcc.WatcherSt) (curRev compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ mvcc.ownStates ST ∗
      ([∗map] w ↦ st ∈ ST, if decide (sint.Z st.minRev < sint.Z compactRev) then
        mvcc.cmpSendPre γ w st.ch ql else iprop(True)) ∗
      ⌜(∀ w, (W !! w).isSome → (ST !! w).isSome) ∧
        ∀ w st, ST !! w = some st → 0 ≤ sint.Z st.minRev ∧
          (sint.Z st.minRev ≤ sint.Z curRev ∨ st.restore = true)⌝ }}
    (App (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"chooseAll")) (Val #curRev))
      (Val #compactRev))
  {{ (minRev : w64), RET #minRev; ∃ Cm : GMap Loc Unit,
      ⌜∀ w, (Cm !! w).isSome → (W !! w).isSome ∧
        ∃ st, ST !! w = some st ∧ sint.Z st.minRev < sint.Z compactRev⌝ ∗
      mvcc.ownWatcherGroup wg (Iris.Std.PartialMap.filter (fun w _ => !(Cm !! w).isSome) W) ∗
      mvcc.ownStates (mvcc.chooseCmp Cm (mvcc.chooseRst curRev (domSet W) ST)) ∗
      ([∗map] w ↦ st ∈ ST, if decide (sint.Z st.minRev < sint.Z compactRev) then
        mvcc.cmpSendPre γ w st.ch ql else iprop(True)) ∗
      ⌜sint.Z minRev = mvcc.minRevOf ST
        (Iris.Std.PartialMap.filter (fun w _ => mvcc.notBehind ST compactRev w) (domSet W))⌝ }}

end spec

end EtcdGrove
end Perennial
