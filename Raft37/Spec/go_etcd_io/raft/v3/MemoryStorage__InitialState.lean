/- `MemoryStorage.InitialState` (`storage.go:121`), specified 2026-10-12 (Lean-first: no
Rocq counterpart). -/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.InitialState()`: the hard state last set (`SetHardState`) and the `ConfState` of
the snapshot, and no error. It takes no lock (it reads `hardState` and `snapshot` and
increments `callStats.initialState` bare): `InitialState` cannot run concurrently with
`SetHardState`, `Snapshot`, `ApplySnapshot` or `CreateSnapshot`, with which it races in Go
although the mutex is documented to protect all fields
(issues/raft-memorystorage-initialstate-unlocked.md).

raft v3.7 (stage R3, 2026-10-15; decision Q6: specified for its single call, at construction,
by `newRaft`). It returns the storage's own pointers: `ms.hardState` (`nil` or read-only,
`hsOpt`) and the snapshot's conf state made whole by `EnsureConfState` (`storage.go:131-133`),
which **writes** the conf state's `AutoLeave` when it is `nil` -- without the lock. So it is
stated on both halves of the storage: `memStorMeta` (the application's: half of `hardState`
and the unlocked counter) and `ownMemoryStorage` (the owner's, which holds the snapshot,
`memSnapOwn`), which at construction one caller holds, before raft starts. The conf state
(holding the storage's `scs`, `sal`: `storCS σ`) is lent at full ownership with its
`AutoLeave` set, with a wand back to `ownMemoryStorage` (`newRaft` reads it in
`confchange.Restore` and `assertConfStatesEquivalent`, then never again); when the snapshot
has no metadata or conf state it is a fresh one (the wand then gives back the storage as it
was). Until the retarget it returned the two values and read only `memStorMeta`'s halves. -/
abbrev MemoryStorage.InitialState.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState) (hs : HardStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      "Hmeta" ∷ memStorMeta ms γs hs }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"InitialState")) (Val #()))
  {{ (hp cs : Loc), RET (PairV (PairV #hp #cs) #interface.nil);
      hsOpt hp hs ∗ memStorMeta ms γs hs ∗
      csPts cs (DFrac.own 1) (storCS σ) true ∗
      (csPts cs (DFrac.own 1) (storCS σ) true -∗ ownMemoryStorage ms γs σ) }}

end spec

end EtcdGrove
end Perennial
