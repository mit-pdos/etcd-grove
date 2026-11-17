/-
**`(*storage.storage).Release(snap)` with its body** (`server/storage/storage.go:75-82`; wal-link L2,
2026-11-17, `notes/wal-link-scope.md` §2, §3.3, decision F1 of etcd-grove-03). Lean-first.

The proof of the triple that replaces `storage.storage.Release.spec` IN PLACE at L3: under the storage's read
lock, the WAL's `ReleaseLockTo(i)` at the snapshot's index `i` (over a share of the WAL's handle and a synced
snapshot record of index `i`, `WAL.ReleaseLockTo.spec`; it returns `nil`), then the snapshotter's
`ReleaseSnapDBs(snap)` (`snap.Snapshotter.ReleaseSnapDBs.spec`, the narrower trust boundary).

Not yet the spec: its clients (`applySnapshot`, `EtcdServer.snapshot`) know the storage only through
`rnNewStorageOk`/`isWalStorage` (trusted until L3), which give neither the storage's representation nor a share
of the WAL's handle. At L3, with that restatement, this statement becomes `storage.storage.Release.spec`
(`Spec/.../storage/storage__Release.lean`, changed in place), this theorem its `wp_proof`, and the axiom
`storage.storage.Release.wp_proof` goes. Until then this theorem is used by nothing (no twin spec: the
axiom's statement is unchanged).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.StorageRep
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReleaseLockTo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__ReleaseSnapDBs
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode storage go_etcd_io.raft.v3 snap
open Fs WalEnc WalFs

section proof
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
removal facts below `i`): `nil`, or an error the snapshotter's directory listing caused. -/
theorem storage.storage.Release.wp_proofNext (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_ReleaseLockTo : go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.spec (Sio := Sio) P Mr)
    (wp_ReleaseSnapDBs : snap.Snapshotter.ReleaseSnapDBs.spec (GF := GF) (hG := hG)) :
    ∀ (p ss : Loc) (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (q : Qp)
      (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (γd : GName)
      (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF) (t : w64) (i n : Nat) (cs : ConfStateM)
      (Q : WalDur → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
        storageOver p w ss ∗ storageRd p w ∗ isSnapshotter ss ∗
        sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
        inv snapDirN (snapDirInv ss γd img Rm) ∗
        □ (∀ j : w64, ⌜uint.Z j < uint.Z md.Index'⌝ -∗ Rm j) ∗
        WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗ WalFs.walSyncedLb dir n ∗
        AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d ∗
            ⌜d.H[i]? = some (WalOpG.snap ⟨cs, md.Index', t⟩) ∧ i < n⌝ }> @ walAuMask, ∅
          <{ WalFs.walDiskAt dir { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) md.Index') },
            COMM Q d }> }}
      (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!!
        go!"Release")) (Val #sn))
    {{ (err : GoInterface), RET #err; storageRd p w ∗
        sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
        walOpenWS Sio P Mr w dir γ q ∗ (∃ d : WalDur, Q d) ∗
        ⌜err = GoInterface.nil ∨ ¬ dirReadOk ss⌝ }} := by
  intro p ss R jr r w dir γ q sn mp dq dq' md γd img Rm t i n cs Q
  wp_start as ⟨#Hover, Hrd, #Hss, HM, Hsm, #Hinv, #HRm, #Harea, Hws, #Hsyn, HAU⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hsnp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap $$ []
  · iPkgInit
  iunfold storageOver at Hover
  icases Hover with ⟨#Hs, #Hguard⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  iunfold storageRd at Hrd
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, >HP⟩
  iunfold storagePw at HP
  (try wp_auto)
  wp_apply wp_GetIndex $$ [$Hrpb $Hsm] as Hsm
  (try wp_auto)
  wp_apply (wp_ReleaseLockTo R jr r w dir γ q md.Index' t i n cs Q) $$ [$Harea $Hws $Hsyn $HAU]
    as %err ⟨%Herr, Hws, HQ⟩
  subst Herr
  (try wp_auto)
  wp_apply (wp_ReleaseSnapDBs ss sn mp dq dq' md γd img Rm) $$ [$Hsnp $Hss $HM $Hsm $Hinv $HRm]
    as %err ⟨HM, Hsm, %Herr⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HP]
  · inext; iunfold storagePw; iexact HP
  iintro Hrd
  wp_auto
  iapply HΦ
  iunfold storageRd
  iframe
  ipureintro; exact Herr

end proof

end EtcdGrove
end Perennial
