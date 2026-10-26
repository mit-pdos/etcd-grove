/- `NewMemoryStorage` (`storage.go:113`), specified 2026-10-10 (Lean-first: no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `NewMemoryStorage()`: `&MemoryStorage{ents: make([]pb.Entry, 1)}`, a storage with
nothing stored (the dummy entry at index `0`), no snapshot and nothing pending
(`memStorEmpty`), under fresh ghost names. Its snapshot is empty, which
`isStorage`'s `Snapshot` clause excludes (`MemstorageInstance.lean`). Since 2026-10-12
also the rest of the storage (`memStorMeta`), at the empty hard state and snapshot, for
`InitialState` and `SetHardState`.

raft v3.7 (stage R3, 2026-10-15): `ents: []*pb.Entry{{}}`, a fresh dummy entry (frozen, as every
stored entry is, `entRO`), `ms.snapshot = EnsureSnapshot(nil)` a fresh zero snapshot the storage
owns, and no hard state (`hardState` is `nil`, the zero record).

D17d (2026-10-18): also the application's snapshot token (`memSnapTok`, at the empty snapshot),
which `ApplySnapshot`, `CreateSnapshot`, `InitialState` and the application's `Snapshot` take.

(2026-10-19, D21 M3) At a cap the caller chooses (`MemStorNames.cap`), at least the empty storage's
boundary `0`: no compaction or applied snapshot passes it.

(D22 S-b′2, 2026-10-20) And the empty certificate registry's authority (`memCertAuth`), which the
application puts in the invariant tying the registry to raft's certificates (`memCertInv`,
`MemstorageInstance.lean`). -/
abbrev NewMemoryStorage.spec : Prop :=
  ∀ (cap : Int), uint.Z (memStorEmpty : StorState).prev.index' ≤ cap →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions NewMemoryStorage [])) (Val #()))
  {{ (ms : Loc) (γs : MemStorNames), RET #ms; ⌜γs.cap = cap⌝ ∗ ownMemoryStorage ms γs memStorEmpty ∗
      memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
      memSnapTok ms γs memStorEmpty ∗ memCertAuth γs }}

end spec

end EtcdGrove
end Perennial
