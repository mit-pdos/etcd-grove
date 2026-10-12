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

end spec

end EtcdGrove
end Perennial
