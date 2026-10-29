/- `MemoryStorage.Snapshot` (`storage.go:207`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). The contract's `Snapshot` triple at the justifications `J` (step 4: the API's). -/
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
  ∀ (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (c : Nat) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      memCompacted γs c ∗ globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Snapshot")) (Val #()))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ⌜err = esu⌝ ∨
      (⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapM snap (DFrac.own 1) sv ∗
        ⌜c ≤ uint.nat sv.Metadata'.Index'⌝ ∗
        (⌜sv.Metadata'.Index' = W64 0⌝ ∨ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index'))) }}

end spec

end EtcdGrove
end Perennial
