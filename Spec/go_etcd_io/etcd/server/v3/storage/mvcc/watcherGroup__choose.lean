/-
`watcherGroup.choose` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchBatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchBatch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__chooseAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `wg.choose(maxWatchers, curRev, compactRev)`, under `chooseAll`'s premise: the group itself
if it has fewer than `maxWatchers` members, else a fresh group of `max 0 maxWatchers` of them
(which ones: the map's iteration order), with the least `minRev` of the group returned. The
group below `2 ^ 63 - 1` members (the fresh group's `add`: its tree's bound); `maxWatchers` not
negative (etcd-io/etcd#22295's `make([]*watcher, 0, maxWatchers)` panics on a negative capacity;
the code before it returned an empty group; the caller passes `maxWatchersPerSync`, `512`). -/
abbrev mvcc.watcherGroup.choose.spec : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange) (ST : GMap Loc mvcc.WatcherSt)
    (maxWatchers curRev compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ mvcc.ownStates ST ∗
      ⌜(∀ w, (W !! w).isSome → (ST !! w).isSome) ∧
        ∀ w st, ST !! w = some st → sint.Z compactRev ≤ sint.Z st.minRev ∧
          sint.Z st.minRev ≤ sint.Z curRev ∧ st.restore = false⌝ ∗
      ⌜GMap.size W + 1 < 2 ^ 63 ∧ 0 ≤ sint.Z maxWatchers⌝ }}
    (App (App (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"choose"))
      (Val #maxWatchers)) (Val #curRev)) (Val #compactRev))
  {{ (g : Loc) (minRev : w64), RET (PairV #g #minRev); mvcc.ownStates ST ∗
      ((⌜g = wg ∧ (GMap.size W : Int) < sint.Z maxWatchers⌝ ∗ mvcc.ownWatcherGroup wg W ∗
          ⌜sint.Z minRev = mvcc.minRevOf ST (domSet W)⌝) ∨
       (∃ W' : GMap Loc mvcc.WatchRange,
          ⌜W' ⊆ W ∧ sint.Z maxWatchers ≤ (GMap.size W : Int) ∧
            (GMap.size W' : Int) = max 0 (sint.Z maxWatchers)⌝ ∗
          mvcc.ownWatcherGroup wg W ∗ mvcc.ownWatcherGroup g W' ∗
          ⌜sint.Z minRev = mvcc.minRevOf ST (domSet W')⌝)) }}

/-- `wg.choose(maxWatchers, curRev, compactRev)` over what `chooseAll` retires
(`chooseAll.specG curRev compactRev Ok P Q`, `Ok` closed under submaps): the group itself,
`chooseAll` run on it, if it has fewer than `maxWatchers` members; else a fresh group of
`maxWatchers` of them `W'`, `chooseAll` run on that, keeping `K ⊆ W'`, and `wg` without the
members `chooseAll` retired (`retireChosen W W' K`: etcd-io/etcd#22295's fix; the code before
it left `wg` at `W`, so a watcher retired with a compaction response stayed in the store's
unsynced group). `spec` is its instance with nothing retired. -/
abbrev mvcc.watcherGroup.choose.specC : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange) (maxWatchers curRev compactRev : w64)
    (Ok : GMap Loc mvcc.WatchRange → Prop) (P : IProp GF)
    (Q : GMap Loc mvcc.WatchRange → GMap Loc mvcc.WatchRange → w64 → IProp GF),
  mvcc.watcherGroup.chooseAll.specG (GF := GF) (hG := hG) curRev compactRev Ok P Q →
  (∀ W1 W2 : GMap Loc mvcc.WatchRange, W1 ⊆ W2 → Ok W2 → Ok W1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ P ∗
      ⌜Ok W ∧ GMap.size W + 1 < 2 ^ 63 ∧ 0 ≤ sint.Z maxWatchers⌝ }}
    (App (App (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"choose"))
      (Val #maxWatchers)) (Val #curRev)) (Val #compactRev))
  {{ (g : Loc) (minRev : w64), RET (PairV #g #minRev);
      (⌜g = wg ∧ (GMap.size W : Int) < sint.Z maxWatchers⌝ ∗
        ∃ K : GMap Loc mvcc.WatchRange, ⌜K ⊆ W⌝ ∗ mvcc.ownWatcherGroup wg K ∗ Q W K minRev) ∨
      (∃ W' K : GMap Loc mvcc.WatchRange,
          ⌜W' ⊆ W ∧ sint.Z maxWatchers ≤ (GMap.size W : Int) ∧
            (GMap.size W' : Int) = sint.Z maxWatchers ∧ K ⊆ W'⌝ ∗
          mvcc.ownWatcherGroup g K ∗ mvcc.ownWatcherGroup wg (mvcc.retireChosen W W' K) ∗
          Q W' K minRev) }}

end spec

end EtcdGrove
end Perennial
