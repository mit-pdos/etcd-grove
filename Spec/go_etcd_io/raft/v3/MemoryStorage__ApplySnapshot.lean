/- `MemoryStorage.ApplySnapshot` (`storage.go:218`), specified 2026-10-12 (Lean-first: no
Rocq counterpart); raft v3.7 (stage R3, 2026-10-15): the snapshot is a pointer, taken owned. -/
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
agrees with the owner's on the snapshot), given back at the new snapshot. -/
abbrev MemoryStorage.ApplySnapshot.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ σt : StorState) (sp : Loc) (sv : SnapshotM)
    (eood : GoInterface),
  σ.pend = [] →
  uint.Z sv.Metadata'.Index' < 2^61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      "Htok" ∷ memSnapTok ms γs σt ∗
      "Hsnap" ∷ ownSnapM sp (DFrac.own 1) sv ∗
      "#Herr" ∷ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot"))
      (Val #sp))
  {{ (err : GoInterface), RET #err;
      ownSnapM sp (DFrac.own 1) sv ∗
      ((⌜σ.ss.index' ≠ W64 0 ∧ uint.Z sv.Metadata'.Index' ≤ uint.Z σ.ss.index' ∧
          err = eood⌝ ∗
        ownMemoryStorage ms γs σ ∗ memSnapTok ms γs σt) ∨
      (⌜¬ (σ.ss.index' ≠ W64 0 ∧ uint.Z sv.Metadata'.Index' ≤ uint.Z σ.ss.index') ∧
          err = interface.nil⌝ ∗
        ownMemoryStorage ms γs (memStorApplied sv) ∗ memSnapTok ms γs (memStorApplied sv))) }}

end spec

end EtcdGrove
end Perennial
