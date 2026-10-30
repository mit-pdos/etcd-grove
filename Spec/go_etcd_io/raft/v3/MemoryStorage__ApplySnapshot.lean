/- `MemoryStorage.ApplySnapshot` (`storage.go:218`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). Takes the owned range from `j ≤ s` (`s` the snapshot's index) to the end, the end, the compaction's justification at `s` (`J.B s`: the API's `snapGiven`), the snapshot's validity and delivered bound, and the stored snapshot open for writes (`memSnapLb γs 0`); always succeeds (the stored snapshot's index is frozen, or `0`, so below `j`, whoever stored it); gives the snapshot `Advance`'s resources: compacted at `s`, the dummy at `s` frozen, the end at `s + 1`, and the stored index at least `s`. `s < 2^61`: the dummy's range bound (the contract's `Hlen`).

kvreconf-snapshot-thread (2026-10-30): no exclusive `memSnapExact` (pre and post): `memSnapLb`. -/
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

/-- `ms.ApplySnapshot(snap)`. -/
abbrev MemoryStorage.ApplySnapshot.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (j : Nat) (old : List EntryM) (sp : Loc)
    (dq : DFrac) (sv : SnapshotM) (eood : GoInterface),
  j ≤ uint.nat sv.Metadata'.Index' →
  uint.nat sv.Metadata'.Index' < 2^61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      memLog γs j (DFrac.own 1) old ∗ memEnd γs (j + old.length) ∗
      J.B (uint.nat sv.Metadata'.Index') ∗ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index') ∗
      snapArg sp dq sv ∗ memSnapLb γs 0 ∗ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp dq sv ∗
      memCompacted γs (uint.nat sv.Metadata'.Index') ∗
      memLog γs (uint.nat sv.Metadata'.Index') DFrac.discard [memDummy sv] ∗
      memEnd γs (uint.nat sv.Metadata'.Index' + 1) ∗ memSnapLb γs (uint.nat sv.Metadata'.Index') }}

end spec

end EtcdGrove
end Perennial
