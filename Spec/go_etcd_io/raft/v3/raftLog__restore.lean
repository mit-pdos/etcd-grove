/-
Port of election_proof/spec_raftLog__restore.v (feb5c73d4).

Lean notes:
* `log_restore` and `snap_id` are `logRestore` and `snapId` (`Defs.lean`).
* The reference `raftLog__restoreⁱᵐᵖˡ` is to the Lean generated code
  `raftLog.restore.impl`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.restore(s)` (`log.go:464`, `raftLog.restore.impl`):

    l.logger.Infof("log [%s] starts to restore snapshot [index: %d, term: %d]", ...)
    l.committed = s.Metadata.Index
    l.unstable.restore(s)

The log becomes the snapshot: `logRestore` (`Defs.lean`) -- `prev` the snapshot's id,
no entries, `committed` its index, `applied` unchanged, the snapshot pending. The
`Storage` is not touched; it is shadowed while the snapshot is pending (`LogStoreOk`,
`InvRaftlog.lean`).

Premises, both for `ownRaftLog` at the new state rather than for the body (which
cannot fail): the snapshot is above the commit index (`raft.restore`'s first test), so
`applied <= committed` survives and the index is non-zero; and its index is below
`2^61`, `LogStoreOk`'s bound for a pending snapshot (a transport premise of `Step`).
The snapshot's `ConfState.Voters` are passed in read-only, for `ownSnap` (since
2026-10-03). (2026-10-15, stage S) The snapshot, with those lists (`snapTrip`), joins the ones
the node may send (`logRestore`'s `ksn`).

raft v3.7 (stage R3, 2026-10-15): `s` is a `*pb.Snapshot`, read at any fraction (its getters,
then `unstable.restore`'s clone) and given back; the lists are the record's
(`sv.Metadata'.ConfState'.lists`; until the retarget the caller's read-only `ConfState` slices,
`ownCSL ... voters`). -/
abbrev raftLog.restore.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (sp : Loc) (dq : DFrac) (sv : SnapshotM),
  uint.Z ls.committed < uint.Z (snapId sv).index' →
  uint.Z (snapId sv).index' < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls ∗
      -- (D22 S-d4 item 4) every pointer field set (`raft.restore`'s `EnsureSnapshot`)
      "Hsnap" ∷ ownSnapS sp dq sv ∗
      -- (D22 S-b′3, 2026-10-20) the snapshot certified in the storage's registry: it joins the
      -- ones the node may send (`ksn`), each of which is (`ownRaftLog`'s `Hkcert`)
      "#Hcert" ∷ storCert ls.storage (snapTrip sv sv.Metadata'.ConfState'.lists) }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"restore")) (Val #sp))
  {{ RET #(); ownSnapS sp dq sv ∗
      ownRaftLog l (logRestore ls (snapTrip sv sv.Metadata'.ConfState'.lists)) }}

end spec

end EtcdGrove
end Perennial
