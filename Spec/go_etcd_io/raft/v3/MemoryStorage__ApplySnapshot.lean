/- `MemoryStorage.ApplySnapshot` (`storage.go:218`), specified 2026-10-12 (Lean-first: no
Rocq counterpart); raft v3.7 (stage R3, 2026-10-15): the snapshot is a pointer, taken owned. -/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Proof.go_etcd_io.raft.v3.InvPbSnapSet

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

/-- `ms.ApplySnapshot(snap)`: unless the storage already has a snapshot at or past `snap`'s
index (`ErrSnapOutOfDate`), the storage is `snap` (`memStorApplied`): its boundary and snapshot
`snap`'s, nothing stored after it. The owner's, with nothing pending (it writes the entries and
the snapshot under the lock, as `Compact` does). The index bound is the storage's
(`ownMemoryStorage`'s `Hbounded`), a client assumption as there.

raft v3.7 (stage R3): `snap` is a `*pb.Snapshot` taken at full ownership (`ownSnapM ... 1`):
`EnsureSnapshot(snap)` fills its nil fields in place (`storage.go:222`; decision Q5). The storage
stores a clone (`proto.Clone(snap)`, 234) and a fresh dummy entry (235), so the caller gets `snap`
back (the same record). Until the retarget the snapshot was a value whose `ConfState` slices the
storage kept (`ownCSL`, the lists `cl`); the lists are now the record's. `memStorMeta` is not
needed any more (it held half of the old snapshot field). D17d (2026-10-18): it changes the
snapshot, so it takes the application's snapshot token too (`memSnapTok`, at any state `σt`: it
agrees with the owner's on the snapshot), given back at the new snapshot.

(D19i part 1, 2026-10-18) The storage's snapshot may be newer than the owner's view of it (the
application's `CreateSnapshot`): the out-of-date test is against the token's, `σt`. The applied
state keeps the owner's floor, which the snapshot must cover; (2026-10-29, stage U8) and its hold,
which the snapshot must cover too (the storage keeps what raft promised: `StorState.hd`).

(D22 S-b′2, 2026-10-20) The new snapshot comes with its certificate in the storage's registry
(`memStorCert`), which the snapshot's home keeps (`memSnapHome`).

(D22 S-d4, 2026-10-21) The snapshot owned, or at any fraction with every pointer field set
(`snapArg`, `ownSnapS`): `EnsureSnapshot` then writes nothing, and the call only reads it -- a
`Ready`'s snapshot, whose other half the node's queued acknowledgement holds (D22 S-d3a), applied
by the application before `Advance`. Given back at the same fraction (`ownSnapM`).

**Logically atomic (D22 J3, 2026-10-26).** In etcd, raft's goroutine calls it while the apply job
may be in `CreateSnapshot`/`Compact` (`notes/j3-overlap-test/`), so the application's token is
shared: its ghost part (`memSnapTokG`, the snapshot and the boundary) is given at the
linearization point (inside the storage's lock, where the storage's snapshot and boundary are the
lock's and the home's), and comes back unchanged (`ErrSnapOutOfDate`, the test against the token's
snapshot) or at the new snapshot. The owner's `ownMemoryStorage` and the argument are given to the
postcondition, after the linearization point. Mask `⊤ \ ↑memSnapN`. The triple of the token in hand
(D17d to D22 J3) is its corollary `MemoryStorage.ApplySnapshot.spec_tok` (`MemstorageAU.lean`). -/
abbrev MemoryStorage.ApplySnapshot.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState) (sp : Loc) (sv : SnapshotM) (dq : DFrac)
    (eood : GoInterface),
  σ.pend = [] →
  uint.Z sv.Metadata'.Index' < 2^61 →
  -- (D19i part 1) the snapshot covers the floor; (2026-10-29, stage U8) the hold, at least the
  -- floor: the storage keeps the entries raft promised
  uint.Z σ.hd ≤ uint.Z sv.Metadata'.Index' →
  -- (2026-10-19, D21 M3) and is within the storage's cap, the new boundary
  uint.Z sv.Metadata'.Index' ≤ γs.cap →
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownMemoryStorage ms γs σ ∗ snapArg sp dq sv ∗
      -- (D22 S-b′2, 2026-10-20) the new snapshot certified in the storage's registry
      memStorCert γs (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
      globalAddr ErrSnapOutOfDate ↦□ eood) -∗
    (|={⊤ \ ↑memSnapN, ∅}=> ∃ σt : StorState, memSnapTokG γs σt ∗
      ((⌜σt.ss.index' ≠ W64 0 ∧ uint.Z sv.Metadata'.Index' ≤ uint.Z σt.ss.index'⌝ -∗
          memSnapTokG γs σt ={∅, ⊤ \ ↑memSnapN}=∗
          (ownSnapM sp dq sv -∗ ownMemoryStorage ms γs σ -∗ Φ #eood)) ∧
       (⌜¬ (σt.ss.index' ≠ W64 0 ∧ uint.Z sv.Metadata'.Index' ≤ uint.Z σt.ss.index')⌝ -∗
          memSnapTokG γs (memStorApplied sv) ={∅, ⊤ \ ↑memSnapN}=∗
          (ownSnapM sp dq sv -∗ ownMemoryStorage ms γs { memStorApplied sv with fl := σ.fl, hd := σ.hd } -∗
            Φ #interface.nil)))) -∗
    WP (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot"))
      (Val #sp)) {{ Φ }}

end spec

end EtcdGrove
end Perennial
