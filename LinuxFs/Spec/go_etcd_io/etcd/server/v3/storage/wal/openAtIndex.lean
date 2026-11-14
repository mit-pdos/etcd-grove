/-
`openAtIndex(lg, dirpath, snap, write)` (S/wal.go:399-440): `selectWALFiles`, `openWALFiles` from the
selected file on, the handle (`NewDecoder` over the readers), and in write mode `parseWALName` of the
tail's name and the pipeline (`newFilePipeline`). Over the WAL layer as `Open` (its spec without
`fileutil.OpenDir`): the update commits where the proof pins the WAL's files (it takes the program's
halves of the segments from the opened one on, and of the WAL directory's claim, out of `walInv`:
the plan's W3/W5 log, decision 2), raising `unl` to `walOpenPos` in write mode (bookkeeping until the
lock model) and changing nothing in read mode. *Success*: write mode, the ghost `walOpening` and the
handle's fields (`walReadH true`), half the call permission (the pipeline holds the other); read
mode, the lock token taken (`walLockedTok`: the handle holds the WAL's halves out of `walParked`) and
`walReadH false` and the whole permission; `dirFile` nil in both. *Error*: the
token and the permission back. Lean-first; proof `sorry`
(`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/openAtIndex.lean`). W5 of
`notes/wal-fsext-plan.md`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
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

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.openAtIndex.spec (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (sp : Loc) (s : w64 × w64) (write : Bool)
    (qp : Qp) (Q : Option WalDur → IProp GF),
  InArea r dir nm → NameOk nm → cleanAbsPath r → dir.length < 2 ^ 59 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      osCallPerm 1 ∗ walSnapIdTerm sp s ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o }> @ walAuMask, ∅
        <{ WalFs.walDirIs dir (if write then o.map (fun d =>
            { d with unl := max d.unl (walOpenPos (d.H.map WalOpG.toM) s.1) }) else o), COMM Q o }> }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.openAtIndex)) (Val #lg))
      (Val #dir)) (Val #sp)) (Val #write))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ ∃ o : Option WalDur, Q o ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ WalFs.walUnlockedTok ∗ osCallPerm 1) ∨
       (⌜err = GoInterface.nil⌝ ∗ ⌜o ≠ none⌝ ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ (null : Loc) ∗
        if write then iprop(WalFs.walOpening w dir s ∗ walReadH true w dir s ∗
          osCallPerm (1 : Qp).half)
        else iprop(WalFs.walLockedTok ∗ walReadH false w dir s ∗ osCallPerm 1))) }}

end spec

end EtcdGrove
end Perennial
