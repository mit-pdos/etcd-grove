/-
`(*storage.storage).Release(snap)` (`server/storage/storage.go:75-82`): under the storage's read lock, the
WAL's `ReleaseLockTo(snap.Metadata.Index)`, then the snapshotter's `ReleaseSnapDBs(snap)`. Proved with its
body in `Proof/.../storage/storage__Release.lean` (wal-link L3, 2026-11-18; until then names-only, an axiom
since D22 receiver epochs, S8d, 2026-10-24, false in its snapshot half: `notes/release-snapdb-held-file.md`;
its replacement was proved at L2 as `wp_proofNext`, decision F1, and is now this spec IN PLACE).
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.StorageRep
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReleaseLockTo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__ReleaseSnapDBs

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI storage go_etcd_io.raft.v3 snap
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **`st.Release(snap)`** of the storage `p` over the WAL `w` and the snapshotter `ss`, with a reader token
(given back) and a share of the WAL's handle (kept): `snap`'s metadata read at index `i = md.Index`, a synced
snapshot record of index `i` in the WAL (the update of `ReleaseLockTo`, which lets the server purge the
segments before the one holding it), and `ReleaseSnapDBs`'s premises (the snapshot directory's invariant at
removal facts below `i`): `nil`, or an error the snapshotter's directory listing caused. (A removed index that
was pending joins the saved set with its removal fact, as in `ReleaseSnapDBs`, D6-T6 2026-11-25.)

Why the WAL half needs the record (`notes/wal-link-scope.md` §3.3, C6): Go's `ReleaseLockTo` compares the
locks' first indices and needs no record, but the server always releases at a snapshot it saved just
before (`server.go:2158/2162`; `raft.go:257` before `applySnapshot`'s `server.go:1122`), so the record its
`SaveSnap` synced meets layer 1's premise. -/
abbrev storage.storage.Release.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
    ∀ (p ss : Loc) (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (q : Qp)
      (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (sd : GoString) (γd : GName)
      (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF) (t : w64) (i n : Nat) (cs : ConfStateM)
      (Q : WalDur → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
        storageOver p w ss ∗ storageRd p w ∗ isSnapshotter ss sd ∗
        sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
        snapDirInvH sd γd img Rm ∗
        □ (∀ j : w64, ⌜uint.Z j < uint.Z md.Index'⌝ -∗ Rm j) ∗
        WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗ WalFs.walSyncedLb dir γ.inc n ∗
        AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir γ.inc d ∗
            ⌜(∃ al, d.H[i]? = some (WalOpG.snap ⟨cs, md.Index', t⟩ al)) ∧ i < n⌝ }> @ walAuMask, ∅
          <{ WalFs.walDiskAtI dir γ.inc { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) md.Index') },
            COMM Q d }> }}
      (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!!
        go!"Release")) (Val #sn))
    {{ (err : GoInterface), RET #err; storageRd p w ∗
        sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
        walOpenWS Sio P Mr w dir γ q ∗ (∃ d : WalDur, Q d) ∗
        ⌜err = GoInterface.nil ∨ ¬ dirReadOk ss⌝ }}

end spec

end EtcdGrove
end Perennial
