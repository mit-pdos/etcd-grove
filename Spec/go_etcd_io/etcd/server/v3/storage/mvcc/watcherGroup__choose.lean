/-
`watcherGroup.choose` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchBatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchBatch

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
(which ones: the map's iteration order), with the least `minRev` of the group returned; the
chosen members above `curRev` have their restore flag cleared (`chooseAll`, D22 receiver epochs
S6). The group below `2 ^ 63 - 1` members (the fresh group's `add`: its tree's bound). -/
abbrev mvcc.watcherGroup.choose.spec : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange) (ST : GMap Loc mvcc.WatcherSt)
    (maxWatchers curRev compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ mvcc.ownStates ST ∗
      ⌜(∀ w, (W !! w).isSome → (ST !! w).isSome) ∧
        ∀ w st, ST !! w = some st → sint.Z compactRev ≤ sint.Z st.minRev ∧
          (sint.Z st.minRev ≤ sint.Z curRev ∨ st.restore = true)⌝ ∗
      ⌜GMap.size W + 1 < 2 ^ 63⌝ }}
    (App (App (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"choose"))
      (Val #maxWatchers)) (Val #curRev)) (Val #compactRev))
  {{ (g : Loc) (minRev : w64), RET (PairV #g #minRev);
      ((⌜g = wg ∧ (GMap.size W : Int) < sint.Z maxWatchers⌝ ∗ mvcc.ownWatcherGroup wg W ∗
          mvcc.ownStates (mvcc.chooseRst curRev (domSet W) ST) ∗
          ⌜sint.Z minRev = mvcc.minRevOf ST (domSet W)⌝) ∨
       (∃ W' : GMap Loc mvcc.WatchRange,
          ⌜W' ⊆ W ∧ sint.Z maxWatchers ≤ (GMap.size W : Int) ∧
            (GMap.size W' : Int) = max 0 (sint.Z maxWatchers)⌝ ∗
          mvcc.ownWatcherGroup wg W ∗ mvcc.ownWatcherGroup g W' ∗
          mvcc.ownStates (mvcc.chooseRst curRev (domSet W') ST) ∗
          ⌜sint.Z minRev = mvcc.minRevOf ST (domSet W')⌝)) }}


end spec

end EtcdGrove
end Perennial
