/- `MemoryStorage.ApplySnapshot` (`storage.go:218`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). Takes the owned range from `j ≤ s` (`s` the snapshot's index) to the end, the end, the compaction's justification at `s` (`J.B s`: the API's `snapGiven`), the snapshot's validity and delivered bound, and the stored snapshot open for writes (`memSnapLb γs 0`); always succeeds (the stored snapshot's index is frozen, or `0`, so below `j`, whoever stored it); gives the snapshot `Advance`'s resources: compacted at `s`, the dummy at `s` frozen, the end at `s + 1`, and the stored index at least `s`. `s < 2^61`: the dummy's range bound (the contract's `Hlen`).

kvreconf-snapshot-thread (2026-10-30): no exclusive `memSnapExact` (pre and post): `memSnapLb`.

Durability stage I (I-5, 2026-10-31): the mode `o` (`memStorAt`; the bounds `J.B s ∗ J.SV sv ∗ J.DL s` are the attached mode's). Detached (`some (c, _)`): the token comes back at compaction point `max c s` and stored snapshot `sv`.

Restart S3 (2026-11-11): a second triple, the snapshot at index `0` (`.2`): v3.7 applies it when the
stored snapshot's index is `0` too (`storage.go:230`, `msIndex != 0`), which etcd's restart does on a
WAL with no snapshot after its initial record (`bootstrappedWAL.MemoryStorage`, `bootstrap.go:741`).
The caller owns the range from `1` (no range can hold the dummy at `0`) and shows the dummy at `0`
frozen as the one the snapshot stores (`memDummy sv`, `NewMemoryStorage`'s when the term is `0`);
the post is the first triple's at `s = 0`.

Restart S6 B2 (2026-11-14, approved by etcd-grove-81): two more triples (`.2.2.1`, `.2.2.2`), the first
two with the token `memSnapNone γs s0` (no write since the storage was made) in place of `memSnapLb γs 0`:
the stored snapshot is not opened, and the token comes back at `sv` (`memSnapNone γs sv`), so that
`Snapshot()` answers `sv` exactly until the client opens it (etcd's restart). -/
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.ApplySnapshot(snap)`: from an owned range at `j ≤ s` (`.1`), or at index `0` from the range
at `1` with the dummy at `0` already the snapshot's (`.2`). -/
abbrev MemoryStorage.ApplySnapshot.spec : Prop :=
  (∀ (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM)) (j : Nat)
    (old : List EntryM) (sp : Loc) (dq : DFrac) (sv : SnapshotM) (eood : GoInterface),
  j ≤ uint.nat sv.Metadata'.Index' →
  uint.nat sv.Metadata'.Index' < 2^61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      memStorAt ms γs J o
        iprop(J.B (uint.nat sv.Metadata'.Index') ∗ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index')) ∗
      memLog γs j (DFrac.own 1) old ∗ memEnd γs (j + old.length) ∗
      snapArg sp dq sv ∗ memSnapLb γs 0 ∗ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp dq sv ∗
      memCompacted γs (uint.nat sv.Metadata'.Index') ∗
      memLog γs (uint.nat sv.Metadata'.Index') DFrac.discard [memDummy sv] ∗
      memEnd γs (uint.nat sv.Metadata'.Index' + 1) ∗ memSnapLb γs (uint.nat sv.Metadata'.Index') ∗
      (match o with
       | some (c, _) => memStorFresh ms γs (max c (uint.nat sv.Metadata'.Index')) sv
       | none => emp) }}) ∧
  (∀ (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM))
    (old : List EntryM) (sp : Loc) (dq : DFrac) (sv : SnapshotM) (eood : GoInterface),
  uint.nat sv.Metadata'.Index' = 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      memStorAt ms γs J o iprop(J.B 0 ∗ J.SV sv ∗ J.DL 0) ∗
      memLog γs 1 (DFrac.own 1) old ∗ memEnd γs (1 + old.length) ∗
      memLog γs 0 DFrac.discard [memDummy sv] ∗
      snapArg sp dq sv ∗ memSnapLb γs 0 ∗ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp dq sv ∗
      memCompacted γs 0 ∗ memLog γs 0 DFrac.discard [memDummy sv] ∗ memEnd γs 1 ∗ memSnapLb γs 0 ∗
      (match o with
       | some (c, _) => memStorFresh ms γs c sv
       | none => emp) }}) ∧
  -- (restart S6 B2, 2026-11-14, approved by etcd-grove-81) the token variants (`.2.2.1`, `.2.2.2`):
  -- with no write since the storage was made (`memSnapNone γs s0`), the stored snapshot stays
  -- unopened, now `sv` (etcd's restart, `bootstrappedWAL.MemoryStorage`, before `run` reads it)
  (∀ (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM)) (j : Nat)
    (old : List EntryM) (sp : Loc) (dq : DFrac) (sv : SnapshotM) (eood : GoInterface) (s0 : SnapshotM),
  j ≤ uint.nat sv.Metadata'.Index' →
  uint.nat sv.Metadata'.Index' < 2^61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      memStorAt ms γs J o
        iprop(J.B (uint.nat sv.Metadata'.Index') ∗ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index')) ∗
      memLog γs j (DFrac.own 1) old ∗ memEnd γs (j + old.length) ∗
      snapArg sp dq sv ∗ memSnapNone γs s0 ∗ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp dq sv ∗
      memCompacted γs (uint.nat sv.Metadata'.Index') ∗
      memLog γs (uint.nat sv.Metadata'.Index') DFrac.discard [memDummy sv] ∗
      memEnd γs (uint.nat sv.Metadata'.Index' + 1) ∗ memSnapNone γs sv ∗
      (match o with
       | some (c, _) => memStorFresh ms γs (max c (uint.nat sv.Metadata'.Index')) sv
       | none => emp) }}) ∧
  (∀ (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM))
    (old : List EntryM) (sp : Loc) (dq : DFrac) (sv : SnapshotM) (eood : GoInterface) (s0 : SnapshotM),
  uint.nat sv.Metadata'.Index' = 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      memStorAt ms γs J o iprop(J.B 0 ∗ J.SV sv ∗ J.DL 0) ∗
      memLog γs 1 (DFrac.own 1) old ∗ memEnd γs (1 + old.length) ∗
      memLog γs 0 DFrac.discard [memDummy sv] ∗
      snapArg sp dq sv ∗ memSnapNone γs s0 ∗ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp dq sv ∗
      memCompacted γs 0 ∗ memLog γs 0 DFrac.discard [memDummy sv] ∗ memEnd γs 1 ∗ memSnapNone γs sv ∗
      (match o with
       | some (c, _) => memStorFresh ms γs c sv
       | none => emp) }})

end spec

end EtcdGrove
end Perennial
