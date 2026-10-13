/- `MemoryStorage.CreateSnapshot` (`storage.go:230`), specified 2026-10-12 (Lean-first: no
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

/-- `ms.CreateSnapshot(i, cs, data)`: unless `i` is at or below the snapshot's index
(`ErrSnapOutOfDate` and an empty snapshot, nothing changed), the snapshot's metadata is
`i` and the term of `i`, its `ConfState` is `*cs` when `cs` is not `nil`, its data
`data` (`memSnapCreated`), and it is returned; the entries are untouched.

The premise: a newer `i` is in the stored log, `prev.index ≤ i ≤ lastIndex`. Above
`lastIndex` `CreateSnapshot` calls `Panicf`; below the compaction boundary
`ms.ents[i-offset]` is out of range (`i - offset` wraps), a runtime panic. Neither
bound is in the method's documentation
(issues/raft-memorystorage-createsnapshot-bounds.md).

Like `ApplySnapshot`, it takes `ownMemoryStorage` with nothing pending and
`memStorMeta`; a non-`nil` `cs` comes with its read-only `Voters` (the stored snapshot's
`ConfState` is the storage's, its slices read-only for good) and is given back. The
error variable's value is passed in, as `Snapshot`'s spec does for its error. -/
abbrev MemoryStorage.CreateSnapshot.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState) (hs : raftpb.HardState)
    (snap : raftpb.Snapshot) (i : w64) (cs : Loc) (dq : DFrac) (c : raftpb.ConfState)
    (data : GoSlice) (eood : GoInterface),
  σ.pend = [] →
  (uint.Z σ.ss.index' < uint.Z i →
    uint.Z σ.prev.index' ≤ uint.Z i ∧
    uint.Z i ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      "Hmeta" ∷ memStorMeta ms γs hs snap ∗
      "Hcs" ∷ (⌜cs = null⌝ ∨ cs ↦{dq} c ∗ ∃ (voters : List w64), c.Voters' ↦*□ voters) ∗
      "#Herr" ∷ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot"))
      (Val #i)) (Val #cs)) (Val #data))
  {{ (snap' : raftpb.Snapshot) (err : GoInterface), RET (PairV #snap' #err);
      (⌜cs = null⌝ ∨ cs ↦{dq} c) ∗
      ((⌜uint.Z i ≤ uint.Z σ.ss.index' ∧ snap' = zero_val raftpb.Snapshot ∧ err = eood⌝ ∗
        ownMemoryStorage ms γs σ ∗ memStorMeta ms γs hs snap) ∨
      (∃ (t : w64), ⌜uint.Z σ.ss.index' < uint.Z i ∧ termAt σ.prev σ.ents i = some t ∧
          snap' = memSnapCreated snap i t (if cs = null then none else some c) data ∧
          err = interface.nil⌝ ∗
        ownMemoryStorage ms γs { σ with ss := snapId snap' } ∗ memStorMeta ms γs hs snap')) }}

end spec

end EtcdGrove
end Perennial
