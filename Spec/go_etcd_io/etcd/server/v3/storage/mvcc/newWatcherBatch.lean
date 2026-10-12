/-
`newWatcherBatch` (`watcher_group.go`). Lean-first (no Rocq counterpart); see `InvWatchBatch.lean`.
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

/-- `newWatcherBatch(wg, evs)`: `nil` if the group is empty, else the batch of each member that
gets an event (`batchOf`: the events its range holds at or above its `minRev`, in order, each
batch a copy of the events sharing their key-values). The members' states (`minRev` is read)
are the caller's: `ST` has those of all members. -/
abbrev mvcc.newWatcherBatch.spec : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange) (ST : GMap Loc mvcc.WatcherSt) (evs : GoSlice)
    (dq : DFrac) (es : List Loc) (evm : List mvcc.EvM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ mvcc.ownStates ST ∗
      ⌜∀ w, (W !! w).isSome → (ST !! w).isSome⌝ ∗
      evs ↦*{dq} es ∗ ([∗list] x ∈ es.zip evm, mvcc.evIs x.1 x.2) ∗ ⌜es.length = evm.length⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherBatch)) (Val #wg))
      (Val #evs))
  {{ (wb : GoMap), RET #wb; mvcc.ownWatcherGroup wg W ∗ mvcc.ownStates ST ∗ evs ↦*{dq} es ∗
      (⌜W = ∅ ∧ wb = map.nil⌝ ∨
        ⌜W ≠ ∅⌝ ∗ mvcc.ownWatcherBatch wb (mvcc.batchOf W ST evm)) }}

end spec

end EtcdGrove
end Perennial
