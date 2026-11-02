/-
`watcherGroup.choose` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchBatch.lean`.
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

/-- `wg.choose(maxWatchers, curRev, compactRev)`: with fewer than `maxWatchers` members, `chooseAll` on
the group itself (`g = wg`); else on a fresh group of `maxWatchers` of them (`max 0 maxWatchers`
for a negative one), `wg` unchanged. The members are as `chooseAll` takes them, and `chooseAll`'s
post holds of the chosen ones `W'`. (Watches across a compaction, 2026-11-01:) the members behind
`compactRev` `chooseAll` sent their compaction response (`Cm`) are deleted from the group it ran
on, so in the copy branch they stay in `wg` (`issues/etcd-watch-compacted-resent.md`). -/
abbrev mvcc.watcherGroup.choose.spec : Prop :=
  ∀ (γ : mvcc.WsNames) (ql : Qp) (wg : Loc) (W : GMap Loc mvcc.WatchRange)
    (ST : GMap Loc mvcc.WatcherSt) (maxWatchers curRev compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ mvcc.ownStates ST ∗
      mvcc.crevPermAt γ.st (sint.Z compactRev) ∗
      ([∗map] w ↦ st ∈ ST, if decide (sint.Z st.minRev < sint.Z compactRev) then
        mvcc.cmpSendPre γ w st.ch ql else iprop(True)) ∗
      ⌜(∀ w, (W !! w).isSome → (ST !! w).isSome) ∧
        ∀ w st, ST !! w = some st → 0 ≤ sint.Z st.minRev ∧
          (sint.Z st.minRev ≤ sint.Z curRev ∨ st.restore = true)⌝ ∗
      ⌜GMap.size W + 1 < 2 ^ 63⌝ }}
    (App (App (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"choose"))
      (Val #maxWatchers)) (Val #curRev)) (Val #compactRev))
  {{ (g : Loc) (minRev : w64), RET (PairV #g #minRev);
      ∃ (W' : GMap Loc mvcc.WatchRange) (Cm : GMap Loc Unit),
        ⌜W' ⊆ W ∧ ∀ w, (Cm !! w).isSome → (W' !! w).isSome ∧
          ∃ st, ST !! w = some st ∧ sint.Z st.minRev < sint.Z compactRev⌝ ∗
        ((⌜g = wg ∧ W' = W ∧ (GMap.size W : Int) < sint.Z maxWatchers⌝ ∗
            mvcc.ownWatcherGroup wg (Iris.Std.PartialMap.filter (fun w _ => !(Cm !! w).isSome) W)) ∨
         (⌜sint.Z maxWatchers ≤ (GMap.size W : Int) ∧
            (GMap.size W' : Int) = max 0 (sint.Z maxWatchers)⌝ ∗
            mvcc.ownWatcherGroup wg W ∗
            mvcc.ownWatcherGroup g (Iris.Std.PartialMap.filter (fun w _ => !(Cm !! w).isSome) W'))) ∗
        mvcc.ownStates (mvcc.chooseCmp Cm (mvcc.chooseRst curRev (domSet W') ST)) ∗
        ([∗map] w ↦ st ∈ ST, if decide (sint.Z st.minRev < sint.Z compactRev) then
          mvcc.cmpSendPre γ w st.ch ql else iprop(True)) ∗
        ⌜sint.Z minRev = mvcc.minRevOf ST
          (Iris.Std.PartialMap.filter (fun w _ => mvcc.notBehind ST compactRev w) (domSet W'))⌝ }}

end spec

end EtcdGrove
end Perennial
