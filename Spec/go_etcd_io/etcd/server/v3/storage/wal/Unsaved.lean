/-
`wal.Unsaved` over `fsExt` (P6 of `notes/etcd-dist-d6.md` §10, item 3; fork `goose-lean-fmt1c-tornsave`,
`server/storage/wal/unsaved.go:36`), with `ValidSnapshotEntries`' binders (the same directory read the same
way: `readWALNames`, every segment opened read-only from the first, decoded to the end). Proved in
`Proof/go_etcd_io/etcd/server/v3/storage/wal/Unsaved.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.UnsavedDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
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

/-- **`Unsaved(lg, dir)`** (unsaved.go:36-94): reads the WAL's names (`readWALNames`), checks that the
first is sequence 0 and index 0 and the sequence numbers consecutive (`isValidSeq`), opens every segment
read-only from the first (`openWALFiles`) and decodes them to the end (`io.EOF` and
`io.ErrUnexpectedEOF` both accepted), returning `false` at a state record, a snapshot record above index
0, or a record after an entry record, and an error at a CRC mismatch or an unknown record type.

`true` (with `nil`) only when there is a WAL at `dir` (`o = some d`) whose history is **blank**
(`walBlank`: every operation a `Save` of no entries and the empty hard state, or a `SaveSnapshot` at
index 0); a blank history's every crash image is blank too (`walBlank_take`). Nothing is claimed of
`false` or of an error: the caller (`bootstrap`, which calls `Discard` only on `true`) then keeps the WAL.

As `ValidSnapshotEntries.spec`: the caller holds the lock token (`walUnlockedTok`, framed), so no
handle is open and the segments do not change while they are read; logically atomic, committed
unchanged at the pin (no step changes the state). -/
abbrev wal.Unsaved.spec (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (qp : Qp) (Q : Option WalDur → IProp GF) (ic : Nat),
  InArea r dir nm → NameOk nm → cleanAbsPath r → PathFits dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      osCallPerm (callKey R r) 1 ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIsI dir ic o }> @ walAuMask, ∅
        <{ WalFs.walDirIsI dir ic o, COMM Q o }> }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Unsaved)) (Val #lg)) (Val #dir))
  {{ (b : Bool) (err : GoInterface), RET (PairV #b #err);
      osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm (callKey R r) 1 ∗ WalFs.walUnlockedTok ∗
      ∃ o : Option WalDur, Q o ∗
      ⌜b = true → err = GoInterface.nil ∧ ∃ d : WalDur, o = some d ∧ walBlank (d.H.map WalOpG.toM)⌝ }}

end spec

end EtcdGrove
end Perennial
