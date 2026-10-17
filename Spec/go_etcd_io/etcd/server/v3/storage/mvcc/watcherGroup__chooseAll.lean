/-
`watcherGroup.chooseAll` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchBatch.lean`.
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

/-- `wg.chooseAll(curRev, compactRev)` of members none of which is below `compactRev`, above
`curRev` or restoring (the store's invariant on the unsynced group; it excludes the compaction
response, the `panic` and the `restore` reset): the least `minRev` of the members,
`math.MaxInt64` if none; nothing changes. -/
abbrev mvcc.watcherGroup.chooseAll.spec : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange) (ST : GMap Loc mvcc.WatcherSt) (curRev compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ mvcc.ownStates ST ∗
      ⌜(∀ w, (W !! w).isSome → (ST !! w).isSome) ∧
        ∀ w st, ST !! w = some st → sint.Z compactRev ≤ sint.Z st.minRev ∧
          sint.Z st.minRev ≤ sint.Z curRev ∧ st.restore = false⌝ }}
    (App (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"chooseAll")) (Val #curRev))
      (Val #compactRev))
  {{ (minRev : w64), RET #minRev; mvcc.ownWatcherGroup wg W ∗ mvcc.ownStates ST ∗
      ⌜sint.Z minRev = mvcc.minRevOf ST (domSet W)⌝ }}

/-- What `wg.chooseAll(curRev, compactRev)` does to its group, abstractly: of members `W`
(`Ok W`), holding `P`, it keeps some `K ⊆ W` (it retires the others, a watcher below
`compactRev` whose compaction response it sent) and gives `Q W K m`, `m` its result. `choose`'s
compaction-aware spec (`mvcc.watcherGroup.choose.specC`) is stated over it; `spec` is an
instance with nothing retired (`spec_G`). The instance that models the compaction response (the
watcher's channel, its `compacted` flag) is not stated: the store is verified frozen. -/
abbrev mvcc.watcherGroup.chooseAll.specG (curRev compactRev : w64)
    (Ok : GMap Loc mvcc.WatchRange → Prop) (P : IProp GF)
    (Q : GMap Loc mvcc.WatchRange → GMap Loc mvcc.WatchRange → w64 → IProp GF) : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ P ∗ ⌜Ok W⌝ }}
    (App (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"chooseAll")) (Val #curRev))
      (Val #compactRev))
  {{ (minRev : w64), RET #minRev; ∃ K : GMap Loc mvcc.WatchRange, ⌜K ⊆ W⌝ ∗
      mvcc.ownWatcherGroup wg K ∗ Q W K minRev }}

/-- `spec` as an instance of `specG`: nothing retired. -/
theorem mvcc.watcherGroup.chooseAll.spec_G (h : mvcc.watcherGroup.chooseAll.spec (GF := GF) (hG := hG))
    (ST : GMap Loc mvcc.WatcherSt) (curRev compactRev : w64) :
    mvcc.watcherGroup.chooseAll.specG (GF := GF) (hG := hG) curRev compactRev
      (fun W => (∀ w, (W !! w).isSome → (ST !! w).isSome) ∧
        ∀ w st, ST !! w = some st → sint.Z compactRev ≤ sint.Z st.minRev ∧
          sint.Z st.minRev ≤ sint.Z curRev ∧ st.restore = false)
      (mvcc.ownStates ST)
      (fun W K m => iprop(⌜K = W ∧ sint.Z m = mvcc.minRevOf ST (domSet W)⌝ ∗ mvcc.ownStates ST)) := by
  intro wg W
  iintro %Φ ⟨#Hpkg, Hg, HST, %Hok⟩ HΦ
  iapply h wg W ST curRev compactRev $$ [Hg HST] [HΦ]
  · iframe Hpkg Hg HST; ipureintro; exact Hok
  inext
  iintro %m ⟨Hg, HST, %Hm⟩
  iapply HΦ
  iexists W
  dsimp only
  iframe Hg HST
  ipureintro
  exact ⟨GMap.map_subseteq_refl _, rfl, Hm⟩

end spec

end EtcdGrove
end Perennial
