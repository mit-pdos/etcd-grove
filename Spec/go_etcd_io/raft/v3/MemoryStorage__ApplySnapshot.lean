/- `MemoryStorage.ApplySnapshot` (`storage.go:218`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). Takes the owned range from `j ≤ s` (`s` the snapshot's index) to the end, the end, the compaction's justification at `s` (`J.B s`: the API's `snapGiven`), the snapshot's validity and delivered bound, and the client's snapshot half; always succeeds (the stored snapshot's index is frozen, so below `j`); gives the snapshot `Advance`'s resources: compacted at `s`, the dummy at `s` frozen, the end at `s + 1`. `s < 2^61`: the dummy's range bound (the contract's `Hlen`). -/
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
    (dq : DFrac) (sv sv0 : SnapshotM) (eood : GoInterface),
  j ≤ uint.nat sv.Metadata'.Index' →
  uint.nat sv.Metadata'.Index' < 2^61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      memLog γs j (DFrac.own 1) old ∗ memEnd γs (j + old.length) ∗
      J.B (uint.nat sv.Metadata'.Index') ∗ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index') ∗
      snapArg sp dq sv ∗ memSnapExact γs sv0 ∗ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp dq sv ∗
      memCompacted γs (uint.nat sv.Metadata'.Index') ∗
      memLog γs (uint.nat sv.Metadata'.Index') DFrac.discard [memDummy sv] ∗
      memEnd γs (uint.nat sv.Metadata'.Index' + 1) ∗ memSnapExact γs sv }}

end spec

end EtcdGrove
end Perennial
