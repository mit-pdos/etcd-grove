/-
`w.ReleaseLockTo(a)` (S/wal.go:1009-1050) over `fsExt` (W9 of `notes/wal-fsext-plan.md`), the main
tree's axiom `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReleaseLockTo.lean` with plan §3's
binders (the area `R jr r`, the update at `walAuMask`). One spec since wal-link L1a (2026-11-17,
`notes/wal-link-scope.md` §8: the former `specNoErr` renamed, the former `spec` its corollary `specR`), over
a share of the handle (`walOpenWS`, `HandleShared.lean`: the server's apply thread releases while the raft
loop saves, serialized by `w.mu`). Proved in `Proof/.../wal/WAL__ReleaseLockTo.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

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
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **`w.ReleaseLockTo(a)`** (S/wal.go:1009-1050): unlocks the files before the lock just before the
first lock named `≥ a` (only the tail stays when none is) and closes them; with a synced snapshot
record of index `a` (at position `i < n`), the update raises the WAL's `unl` mark to
`walReleasePos H a` (the main tree's axiom: every record from there on stays in a locked file). The
raise commits at the call's first step, right after `w.mu.Lock()`; the handle raises its registered
locked range with it (unit `locks`, session 5: `walInv_releaseLks`), and the locks it closes are of
segments ending at or before the new mark (`cutStart_le_releasePos`), which is what a purger relies on
(`walDirLks`, `walLksAuth`). It returns `nil`: its only error is `parseWALName` rejecting a lock's file
name, and every lock of the handle is a segment's (`walLockH`'s `walSegName`, the tail's `walDirH`); the
locks' `Close` errors are ignored by the code (S/wal.go:1013-1053). No I/O premise. The closed locks'
fds go with them; the share is kept. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.spec (P : WalPbIn GF) (Mr : WalMarshal) :
    Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (q : Qp) (a t : w64)
    (i n : Nat) (cs : ConfStateM) (Q : WalDur → IProp GF),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗ WalFs.walSyncedLb dir γ.inc n ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir γ.inc d ∗ ⌜(∃ al, d.H[i]? = some (WalOpG.snap ⟨cs, a, t⟩ al)) ∧ i < n⌝ }>
        @ walAuMask, ∅
        <{ WalFs.walDiskAtI dir γ.inc { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) a) },
          COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
      go!"ReleaseLockTo")) (Val #a))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ walOpenWS Sio P Mr w dir γ q ∗ ∃ d : WalDur, Q d }}

/-- **`ReleaseLockTo.spec` with the result forgotten** (a client that does not look at it; a corollary,
`ReleaseLockTo.spec_R`). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.specR (P : WalPbIn GF) (Mr : WalMarshal) :
    Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (q : Qp) (a t : w64)
    (i n : Nat) (cs : ConfStateM) (Q : WalDur → IProp GF),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗ WalFs.walSyncedLb dir γ.inc n ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir γ.inc d ∗ ⌜(∃ al, d.H[i]? = some (WalOpG.snap ⟨cs, a, t⟩ al)) ∧ i < n⌝ }>
        @ walAuMask, ∅
        <{ WalFs.walDiskAtI dir γ.inc { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) a) },
          COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
      go!"ReleaseLockTo")) (Val #a))
  {{ (err : GoInterface), RET #err; walOpenWS Sio P Mr w dir γ q ∗ ∃ d : WalDur, Q d }}

end spec

end EtcdGrove
end Perennial
