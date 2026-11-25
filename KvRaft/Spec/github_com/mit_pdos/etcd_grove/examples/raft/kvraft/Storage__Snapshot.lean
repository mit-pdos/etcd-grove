-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/Storage__Snapshot.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`s.Snapshot()` (storage.go): the `MemoryStorage`'s snapshot, or, one time in four,
`ErrSnapshotTemporarilyUnavailable` (`esu`). Attached mode (what raft's storage contract calls):
kvreconf's `Storage.Snapshot.spec` at kvdurable's wrapper (`kdStorRec`). (2026-11-01, stage II (j),
S4.)
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

/-- See the file header. -/
abbrev Storage.Snapshot.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (c : Nat) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      kdStorRec s ms γs ∗ memStorInvP ms γs J ∗ memCompacted γs c ∗
      globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"Snapshot")) (Val #()))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ⌜err = esu⌝ ∨
      ⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapM snap (DFrac.own 1) sv ∗
        ⌜c ≤ uint.nat sv.Metadata'.Index'⌝ ∗
        (⌜sv.Metadata'.Index' = W64 0⌝ ∨ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index')) }}

end spec

end kvraft
end EtcdGrove
end Perennial
