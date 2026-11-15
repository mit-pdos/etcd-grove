/- `MemoryStorage.Snapshot` (`storage.go:207`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). The contract's `Snapshot` triple at the justifications `J` (step 4: the API's), `b = false`; with `b = true`, given `memSnapNone` (no snapshot stored yet: etcd's `run` at boot, which panics on anything else), the answer is exactly the empty snapshot.

kvreconf-snapshot-thread (2026-10-30, R1 of the repair design): `b` and `memSnapNone` added.

Durability stage I (I-5, 2026-10-31): the mode `o` (`memStorAt`). Attached (`none`): as before. Detached (`some (c0, sv0)`): the clone is the stored snapshot `sv0` exactly, and the token comes back.

Restart S6 B2 (2026-11-14, approved by etcd-grove-81): the token `t` generalizes `b`: `none` is `b = false`;
`some sv₀` (`memSnapNone γs sv₀`: no write since the storage was made, `NewMemoryStorage`'s at the empty
snapshot, `ApplySnapshot`'s token variant's at the snapshot it stored) answers exactly `sv₀`. A first
start is the instance `sv₀ = memSnapEmpty`; a restart's, the WAL's snapshot. -/
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

/-- `ms.Snapshot()`: a clone of the stored snapshot, at or past what the caller knows is
compacted, empty or valid with its delivered bound. (`ErrSnapshotTemporarilyUnavailable` is
never returned; the disjunct is the contract's.) -/
abbrev MemoryStorage.Snapshot.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM)) (c : Nat)
    (t : Option SnapshotM) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorAt ms γs J o emp ∗
      memCompacted γs c ∗ (match t with | some s => memSnapNone γs s | none => emp) ∗
      globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Snapshot")) (Val #()))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      (match t with | some s => memSnapNone γs s | none => emp) ∗
      -- (2026-10-30, the repair) never an error: `MemoryStorage.Snapshot` returns `nil` (the
      -- `Storage` contract, `isStorageP`, keeps admitting `ErrSnapshotTemporarilyUnavailable` for
      -- wrappers); `esu` is unread; and the clone whole (`ownSnapW`: its metadata and conf state
      -- set, `EnsureSnapshot`'s), which etcd's `run` reads directly
      ⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapW snap (DFrac.own 1) sv ∗
         ⌜c ≤ uint.nat sv.Metadata'.Index' ∧ (∀ s, t = some s → sv = s)⌝ ∗
         (match o with
          | some (c0, sv0) => iprop(⌜sv = sv0⌝ ∗ memStorFresh ms γs c0 sv0)
          | none => iprop(⌜sv.Metadata'.Index' = W64 0⌝ ∨ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index'))) }}

end spec

end EtcdGrove
end Perennial
