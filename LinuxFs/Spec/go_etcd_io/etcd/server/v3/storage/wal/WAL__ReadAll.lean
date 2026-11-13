/-
`(*wal.WAL).ReadAll` over `fsExt` (W3 of `notes/wal-fsext-plan.md`): the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReadAll.lean` restated with plan §3's binder changes
(over `fsExt`, the WAL layer `walAreaOk`, the handles `walOpeningF`/`walReadFailedF`/`walOpenWF`,
the update at `walAuMask`, plan §11), its success post restated (`walReadAllOk` in place of
`walReadCut … = some σ`: `notes/specs-only/ledger.md`, 2026-11-13; `WalReadAllPost.lean`), and
the raft messages it returns through `WalPbIn` (`P.hsIn`, `walEntsIn`; the main tree's
`walSaveEnts false` dropped: `entIn` carries no size cache, so I9 does not arise). S/ =
`server/storage/wal/` at the pin with the local fork patches. To be proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReadAll.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalReadAllPost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`w.ReadAll()`** (S/wal.go:512-684, write mode, with F-Z and F-N4): from the newest valid
snapshot `s` (the atomic precondition's premise, as the main tree's), decode every record of the
files `Open` selected (`decoder.Decode` to `io.EOF`; a torn or corrupt tail is an error: plan
§2.5), fold them (`readAllFold`, `WalEncFold.lean`), then zero the tail past the last record
(`ZeroToEnd`) and fdatasync it (F-Z, needed under power loss: plan §2.4 item 2), fsync the WAL
directory and the area (F-N4: `walNamed`), and make the encoder at the decoder's CRC.

*Success*: the read is `walReadAllOk` of the history (the fold from a position between the read
position and `walOpenPos`, at the fixed base `s`); the handle appends (`walOpenWF`), the history is
synced (`walSyncedLb`) and named (`walNamed`), the handle's length fact and purge right. *Error*
(an I/O error, a record the fold rejects, `ErrSnapshotNotFound`/`ErrSnapshotMismatch`): the handle is
failed (`walReadFailedF`, only `Close` takes it). Both arms give `Q d`: the history is not changed,
so the update commits wherever the proof reads the state (the synced mark and `named` raised by the
syncs are lower bounds the program's copy may lag). The area's spine and a call permission are
framed (`syncDir(filepath.Dir(dir))` opens the area). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.ReadAll.spec (P : WalPbIn GF) (Mr : WalMarshal) :
    Prop :=
  ∀ (R : Roots) (jr : Ino) (r dir nm : GoString) (w : Loc) (s : w64 × w64) (qp qc : Qp)
    (Q : WalDur → IProp GF),
  InArea r dir nm → cleanAbsPath r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ osCallPerm qc ∗
      walOpeningF w dir s ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d ∗
          ⌜some s = walNewestPair (walValidSnaps (d.H.map WalOpG.toM) d.cut)⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir d, COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"ReadAll"))
      (Val #()))
  {{ (mdp : GoSlice) (hp : Loc) (sl : GoSlice) (err : GoInterface),
      RET (PairV (PairV (PairV #mdp #hp) #sl) #err);
      osPathS R r (DFrac.own qp) jr ∗ osCallPerm qc ∗ ∃ d : WalDur, Q d ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ walReadFailedF w dir) ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ (σ : StorContents) (esL : List Loc),
        ⌜walReadAllOk (d.H.map WalOpG.toM) d.cut s σ⌝ ∗ P.hsIn hp σ.hs ∗ sl ↦*□ esL ∗
        walEntsIn P esL σ.ents ∗ mdp ↦*□ d.metadata ∗ walOpenWF P Mr w dir ∗
        WalFs.walNamed dir ∗ WalFs.walSyncedLb dir d.H.length ∗ WalFs.walLenLb w dir d.H.length ∗
        WalFs.walPurgeW w dir)) }}

end spec

end EtcdGrove
end Perennial
