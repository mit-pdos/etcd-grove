/- Lean-first (no Rocq counterpart).

`(*Storage).Snapshot()` (kv.go): the `MemoryStorage`'s snapshot, but
`ErrSnapshotTemporarilyUnavailable` for an empty one (a storage that never had one).

2026-10-30 (stage F of the client repair, kvreconf's `Storage.Snapshot.spec`):
`MemoryStorage.Snapshot.spec` at the wrapper (`kvStorRec`), as `isStorage`'s `HSnapshot` clause
(`InvStorage.lean`) asks of the method: the embedded storage's answer -- a fresh owned clone
(`ownSnapM`), at or past the known compaction point, empty or valid and delivered (`J.SV`,
`J.DL`) -- or `ErrSnapshotTemporarilyUnavailable` (`esu`). Until then over the owner's view
(`ownMemoryStorage`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev Storage.Snapshot.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (c : Nat) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      kvStorRec s ms γs ∗ memStorInvP ms γs J ∗ memCompacted γs c ∗
      globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (s @!! go.GoType.PointerType rStorageTy @!! go!"Snapshot")) (Val #()))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ⌜err = esu⌝ ∨
      ⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapM snap (DFrac.own 1) sv ∗
        ⌜c ≤ uint.nat sv.Metadata'.Index'⌝ ∗
        (⌜sv.Metadata'.Index' = W64 0⌝ ∨ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index')) }}

end spec

end kv
end EtcdGrove
end Perennial
