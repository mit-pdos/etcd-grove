/- `MemoryStorage.CreateSnapshot` (`storage.go:243`), specified 2026-10-12 (Lean-first: no
Rocq counterpart); raft v3.7 (stage R3, 2026-10-15): pointers, the storage's snapshot written in
place, clones in and out. -/
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
(`ErrSnapOutOfDate` and a `nil` snapshot, nothing changed), the snapshot's metadata is
`i` and the term of `i`, its `ConfState` is `*cs` when `cs` is not `nil`, its data
`data` (`memSnapCreated`), and a clone of it is returned; the entries are untouched.

The premise: a newer `i` is in the stored log, `prev.index ≤ i ≤ lastIndex`. Above
`lastIndex` `CreateSnapshot` calls `Panicf`; below the compaction boundary
`ms.ents[i-offset]` is out of range (`i - offset` wraps), a runtime panic. Neither
bound is in the method's documentation
(issues/raft-memorystorage-createsnapshot-bounds.md).

Like `ApplySnapshot`, it takes `ownMemoryStorage` with nothing pending. The error variable's
value is passed in, as `Snapshot`'s spec does for its error.

The `ConfState` (2026-10-14, reconfiguration stage B8): the one stored is exactly `*cs`
(`memSnapCreated_confState`; the previous one when `cs = nil`), at the id `(t, i)`
(`memSnapCreated_snapId`). So the application's obligation A3, that a snapshot's `ConfState`
is the configuration of its prefix and its index at most the applied one (`SnapObl`,
`SnapConf.lean`), is a statement about `c`'s lists and `i`, which the application proves
before the call.

raft v3.7 (stage R3, 2026-10-15): `CreateSnapshot` now writes the storage's own snapshot in
place (`EnsureSnapshot(ms.snapshot)`, then `Metadata.Index`/`Term` replaced by fresh cells,
`storage.go:255-257`), stores a **clone** of `*cs` (259) and the caller's `data` slice itself
(261), and returns a fresh clone of the result (262), owned by the caller; on the error path it
returns `nil` (until the retarget a zero snapshot value). So `cs` is read at any fraction
(`ownCSM cs dq c`, given back; until the retarget its slices were kept by the storage,
read-only, `ownCSL`), and the bytes of `data` are taken (`data ↦* bs`, full: the storage's
snapshot owns them; given back on the error path). `memStorMeta` is not needed any more. -/
abbrev MemoryStorage.CreateSnapshot.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState) (i : w64) (cs : Loc) (dq : DFrac)
    (oc : Option ConfStateM) (data : GoSlice) (bs : List w8) (eood : GoInterface),
  σ.pend = [] →
  (uint.Z σ.ss.index' < uint.Z i →
    uint.Z σ.prev.index' ≤ uint.Z i ∧
    uint.Z i ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      "Hcs" ∷ (match oc with
               | none => iprop(⌜cs = null⌝)
               | some c => ownCSM cs dq c) ∗
      "Hdata" ∷ data ↦* bs ∗
      "#Herr" ∷ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot"))
      (Val #i)) (Val #cs)) (Val #data))
  {{ (snap' : Loc) (err : GoInterface), RET (PairV #snap' #err);
      (match oc with
       | none => iprop(⌜cs = null⌝)
       | some c => ownCSM cs dq c) ∗
      ((⌜uint.Z i ≤ uint.Z σ.ss.index' ∧ snap' = null ∧ err = eood⌝ ∗
        ownMemoryStorage ms γs σ ∗ data ↦* bs) ∨
      (∃ (t : w64), ⌜uint.Z σ.ss.index' < uint.Z i ∧ termAt σ.prev σ.ents i = some t ∧
          err = interface.nil⌝ ∗
        ownSnapM snap' (DFrac.own 1) (memSnapCreated σ i t oc bs) ∗
        ownMemoryStorage ms γs { σ with ss := entryID.mk t i,
                                        scs := (memSnapCreated σ i t oc bs).Metadata'.ConfState'.lists,
                                        sal := (memSnapCreated σ i t oc bs).Metadata'.ConfState'.AutoLeave' })) }}

end spec

end EtcdGrove
end Perennial
