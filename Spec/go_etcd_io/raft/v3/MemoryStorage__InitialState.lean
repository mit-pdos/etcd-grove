/- `MemoryStorage.InitialState` (`storage.go:121`), specified 2026-10-12 (Lean-first: no
Rocq counterpart). -/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

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
(holding the storage's `scs`, `sal`: `storCS σ`) is returned read-only for good with its
`AutoLeave` set (`csPts cs □ _ true`), beside the storage as it was (D7, stage R4: the storage's
snapshot now holds it frozen, `csOptA`'s third case; nothing writes a conf state in place once
its `AutoLeave` is set). `newRaft` reads it in `confchange.Restore` and
`assertConfStatesEquivalent` while it reads the log, which holds the storage, so the conf state
cannot be lent with a wand back to the storage (R3's statement until D7). When the snapshot has
no metadata or conf state it is a fresh one, frozen likewise. Until the retarget it returned the
two values and read only `memStorMeta`'s halves.

D17d (2026-10-18): the snapshot lives under the lock (`memSnapInv`), and `InitialState` reads it
without the lock, so it takes the application's snapshot token (`memSnapTok`) beside the owner's
`ownMemoryStorage`: the two keys together lend it the snapshot (no locked `Snapshot`,
`ApplySnapshot` or `CreateSnapshot` can run meanwhile: each needs one of them). `StartNode` and
`RestartNode` call it (through `newRaft`) before they start the node's goroutine; the token comes
back unchanged. -/
abbrev MemoryStorage.InitialState.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ σt : StorState) (hs : HardStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      "Hmeta" ∷ memStorMeta ms γs hs ∗
      "Htok" ∷ memSnapTok ms γs σt }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"InitialState")) (Val #()))
  {{ (hp cs : Loc), RET (PairV (PairV #hp #cs) #interface.nil);
      hsOpt hp hs ∗ memStorMeta ms γs hs ∗ ownMemoryStorage ms γs σ ∗ memSnapTok ms γs σt ∗
      csPts cs DFrac.discard (storCS σ) true }}

end spec

end EtcdGrove
end Perennial
