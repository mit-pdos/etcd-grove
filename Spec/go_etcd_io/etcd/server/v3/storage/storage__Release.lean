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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **`st.Release(snap)`** of the server's storage `p` over the snapshotter `ss` (`storageSnap`),
`snap`'s metadata read-only at index `i = md.Index`, the snapshot directory's invariant at any
removal fact `Rm`, with `Rm j` for every `j < i`: `nil`, or an error the environment caused
(`¬ releaseOk`).

Why it is true of the Go code (`storage.go:75-82` at the etcd pin, and `wal.ReleaseLockTo`,
`snap.Snapshotter.ReleaseSnapDBs`): under the storage's read lock, the WAL's `ReleaseLockTo(i)`
closes and drops the lock files of the WAL segments before the one holding `i` (the WAL's own
state, read by nothing the model tracks), then `ReleaseSnapDBs(snap)` lists `ss`'s directory and
removes each `<j>.snap.db` with `j < i`: in the invariant, each removed file leaves `M` with its
removal fact `Rm j`, given for every `j < i`; no other file is touched, and the transport's
`SaveDBFrom` adds files only under the invariant. An error is returned only from a failed close or
removal (I/O).

(D22 J4, 2026-10-26; decided by the orchestrator while the user was away (J5/J4), J0's item 3) Over
any `Rm`, the removal facts below `i` given; until J4 the removal fact was `snapTakenLb γt` and the
premise `snapTakenLb γt i` (from which `Rm j = snapTakenLb γt j` followed for `j < i`): a special
case (`applySnapshot`'s own `Release`, after the open); `snapshot`'s `Release` at the applied index
has the facts from the applied index instead (J0's `Rm j := snapTakenLb γt j ∨ appliedAtLeast γr
(j + 1)`). -/
abbrev storage.storage.Release.spec : Prop :=
  ∀ (p ss sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (γd : GName)
    (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF),
  storageSnap p ss →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
      inv snapDirN (snapDirInv ss γd img Rm) ∗
      □ (∀ j : w64, ⌜uint.Z j < uint.Z md.Index'⌝ -∗ Rm j) }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!!
      go!"Release")) (Val #sn))
  {{ (err : GoInterface), RET #err; sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
      smOpt mp dq' md ∗ ⌜err = GoInterface.nil ∨ ¬ releaseOk⌝ }}

end spec

end EtcdGrove
end Perennial
