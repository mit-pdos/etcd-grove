/-
`(*storage.storage).Release(snap)` (`server/storage/storage.go`): names-only. Lean-first (no Rocq
counterpart); D22 receiver epochs, S8d (2026-10-24), for `applySnapshot`; an axiom at the trust
boundary (`Proof/.../storage/storage__Release.lean`), why it is true of the Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI backend storage go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **`st.Release(snap)`** of the server's storage `p` over the snapshotter `ss` (`storageSnap`),
`snap`'s metadata read-only at index `i = md.Index`, a snapshot at index `i` or above opened
(`snapTakenLb γt i`), the snapshot directory's invariant with the server's removal fact
(`Rm := snapTakenLb γt`): `nil`, or an error the environment caused (`¬ releaseOk`).

Why it is true of the Go code (`storage.go:75-82` at the etcd pin, and `wal.ReleaseLockTo`,
`snap.Snapshotter.ReleaseSnapDBs`): under the storage's read lock, the WAL's `ReleaseLockTo(i)`
closes and drops the lock files of the WAL segments before the one holding `i` (the WAL's own
state, read by nothing the model tracks), then `ReleaseSnapDBs(snap)` lists `ss`'s directory and
removes each `<j>.snap.db` with `j < i`: in the invariant, each removed file leaves `M` with its
removal fact `Rm j = snapTakenLb γt j`, which follows from `snapTakenLb γt i` (`j < i`); no other
file is touched, and the transport's `SaveDBFrom` adds files only under the invariant. An error is
returned only from a failed close or removal (I/O). -/
abbrev storage.storage.Release.spec : Prop :=
  ∀ (p ss sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (γd γt : GName)
    (img : w64 → backend.Data → IProp GF),
  storageSnap p ss →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
      inv snapDirN (snapDirInv ss γd img (snapTakenLb γt)) ∗ snapTakenLb γt md.Index' }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!!
      go!"Release")) (Val #sn))
  {{ (err : GoInterface), RET #err; sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
      smOpt mp dq' md ∗ ⌜err = GoInterface.nil ∨ ¬ releaseOk⌝ }}

end spec

end EtcdGrove
end Perennial
