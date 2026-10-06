/-
Port of `election_proof/spec_raftLog__snapshot.v`.

Lean notes:
* Rocq's `(#snap, #err)` is `PairV #snap #err`; `global_addr` is `globalAddr`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.snapshot()` -- the snapshot the log can offer a lagging peer
(`raftLog.snapshot.impl`, `Perennial/Code/go_etcd_io/raft/v3.lean`):

    if l.unstable.snapshot != nil { return *l.unstable.snapshot, nil }
    return l.storage.Snapshot()

`ownRaftLog`'s `Hnosnap` says the unstable snapshot is always `nil` on this path (no
snapshot is ever received -- see `InvRaftlog.lean`), so the first branch is dead and
the result is exactly what the client-supplied `Storage` returns. The postcondition is
therefore `isStorage`'s `HSnapshot` clause verbatim (`InvStorage.lean`): either the
distinguished `ErrSnapshotTemporarilyUnavailable` -- whose points-to the caller passes
in, since the comparison in `maybeSendSnapshot` is against the package-level variable,
not against a claim about `errors.New` -- or success with a snapshot whose
`Metadata.Index` is non-zero.

The log comes back at the same state, like `raftLog.firstIndex`: the one caller,
`raft.maybeSendSnapshot`, calls both on the same log. -/
abbrev raftLog.snapshot.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls ∗
      "#Hesu" ∷ globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"snapshot")) (Val #()))
  {{ (snap : raftpb.Snapshot) (err : GoInterface), RET (PairV #snap #err);
      ownRaftLog l ls ∗
      ⌜err = esu ∨
        (err = interface.nil ∧ snap.Metadata'.Index' ≠ W64 0)⌝ }}

end spec

end EtcdGrove
end Perennial
