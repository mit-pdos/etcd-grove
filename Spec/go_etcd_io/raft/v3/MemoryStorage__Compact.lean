/- `MemoryStorage.Compact` (`storage.go:271`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). Takes the frozen entry at `x`, or `x` already compacted (then `ErrCompacted`: etcd's periodic compaction after an install), the compaction's justification at `x` (`J.B x`: the API's `nodeAppliedLb`), and `x` at most the stored snapshot's index (`memSnapLb γs x`).

kvreconf-snapshot-thread (2026-10-30): `memSnapLb γs x` in place of the exclusive `memSnapExact γs sv0` with `x ≤ sv0`'s index. -/
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.Compact(x)`. -/
abbrev MemoryStorage.Compact.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (x : w64) (ecomp : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      ((∃ (e : EntryM), memLog γs (uint.nat x) DFrac.discard [e]) ∨ memCompacted γs (uint.nat x)) ∗
      J.B (uint.nat x) ∗ memSnapLb γs (uint.nat x) ∗ globalAddr ErrCompacted ↦□ ecomp }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Compact")) (Val #x))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil ∨ err = ecomp⌝ ∗ memCompacted γs (uint.nat x) }}

end spec

end EtcdGrove
end Perennial
