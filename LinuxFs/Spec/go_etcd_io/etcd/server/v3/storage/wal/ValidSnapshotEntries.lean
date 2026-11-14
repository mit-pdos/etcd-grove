/-
`wal.ValidSnapshotEntries` over `fsExt` (W8 of `notes/wal-fsext-plan.md`; the W7-W12 log, W8): the main
tree's axiom `Spec/go_etcd_io/etcd/server/v3/storage/wal/ValidSnapshotEntries.lean` restated with plan §3's
binders (over `fsExt`: the WAL layer `walAreaOk`, the area's spine and `walAreaRes`, the call permission, the
update at `walAuMask`, plan §11), as `Repair`'s and `OpenForRead`'s (the same directory read the same way:
`readWALNames`, then every segment opened read-only). S/ = `server/storage/wal/` at the pin with the local fork
patches. Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/ValidSnapshotEntries.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Spec.go_uber_org.zap.Defs

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

/-- **`ValidSnapshotEntries(lg, dir)`** (S/wal.go:698-791): up to three attempts of
`validSnapshotEntries` (the retry on an error `errors.Is` takes for `os.ErrNotExist`), each reading the
WAL's names (`readWALNames`), opening every segment read-only (`openWALFilesFn`, `openWALFiles` in read
mode, from the first), decoding them to the end (`io.EOF` and `io.ErrUnexpectedEOF` both accepted) and
keeping the snapshot records at or below the last state record's commit. Its result is
`walValidSnaps` of the history from the read position `cut` (the first remaining segment's start), or
an error; with no WAL at `dir` (`o = none`) it fails (`readWALNames`).

The caller holds the lock token (`walUnlockedTok`, framed, as the main tree's: W4a.1, finding F-W4b-2):
no handle of the generation is open, so the whole history is in the segments and no segment changes
while they are read (the token pins them: the program's halves of the segments and of the directory's
claim, `walParked`), nor does a purge remove one (so the retry loop never sees a removed file, but the
proof does not need that: every attempt reads the same pinned files). Logically atomic, committed
unchanged at the pin (no step changes the state), as `Repair`'s. -/
abbrev wal.ValidSnapshotEntries.spec (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (qp : Qp) (Q : Option WalDur → IProp GF),
  InArea r dir nm → NameOk nm → cleanAbsPath r → dir.length < 2 ^ 59 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      osCallPerm 1 ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o }> @ walAuMask, ∅
        <{ WalFs.walDirIs dir o, COMM Q o }> }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.ValidSnapshotEntries)) (Val #lg)) (Val #dir))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm 1 ∗ WalFs.walUnlockedTok ∗
      ∃ o : Option WalDur, Q o ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ∃ (d : WalDur) (ps : List Loc), ⌜o = some d⌝ ∗ sl ↦*□ ps ∗
        walSnapsAt ps (walValidSnaps (d.H.map WalOpG.toM) d.cut)) }}

end spec

end EtcdGrove
end Perennial
