/-
`wal.Repair` over `fsExt` (W7 of `notes/wal-fsext-plan.md`; the W7-W12 log, fifth session): the main
tree's axiom `Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean` restated with plan §3's binders (over
`fsExt`: the WAL layer `walAreaOk`, the area's spine and `walAreaRes`, the call permission, the update at
`walAuMask`, plan §11) and §6 Q7 (the lock token, framed; `notes/specs-only/ledger.md`, 2026-11-14). `Open`'s
binders, as `Repair` reads the same directory (`openLast`: `readWALNames`, `fileutil.LockFile` of the last
name). S/ = `server/storage/wal/` at the pin with the local fork patches. Not yet proved (the proof plan, its
callee specs and the invariant laws it needs: the W7-W12 log, fifth session). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenLastDefs
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

/-- **`Repair(lg, dir)`** (S/repair.go:30-106): `openLast` (`readWALNames`, then `fileutil.LockFile` of the
last segment, read-write), the decoder over it until an error; on `io.EOF` true; on
`io.ErrUnexpectedEOF` a copy of the segment to `<segment>.broken` (`createNewWALFile`, `Seek`, `io.Copy`),
the segment truncated at the last record's end and fsynced, true; otherwise false. The records the WAL's
history decodes to are unchanged: the decoder accepts exactly the frames of the last segment's stream
(the invariant's crash condition, W1: no frame past it passes the CRC), so the truncation is at the
stream's end and removes no record of the history; the state is unchanged. Logically atomic, committed as accessed (no step changes the
state). With the lock token, framed (plan §6 Q7: with the trivial lock model, `LockFile` waits for
nothing, so a concurrent appender would race the truncation; both callers, the WAL tester and
`openWALFromSnapshot`, call `Repair` after a successful `Close`; the main tree's "blocks until the
handle's `Close`" scenario is dropped until the lock model). The boolean claims nothing, as the main
tree's. On `false` the token may be lost (`notes/specs-only/ledger.md`, 2026-11-14, "the `false` arm after a
failed `Truncate` or `Fsync`"; plan §6 Q6): after a failed truncate or fsync of the last segment the
truncate's window stays open and the tail `Repair` registered cannot be unregistered; every client stops on
`false` (the WAL tester's `restartRead`, etcd's `openWALFromSnapshot`: `lg.Fatal`). -/
abbrev wal.Repair.spec (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (qp : Qp) (Q : Option WalDur → IProp GF) (ic : Nat),
  InArea r dir nm → NameOk nm → cleanAbsPath r → PathFits dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      osCallPerm (callKey R r) 1 ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIsI dir ic o }> @ walAuMask, ∅
        <{ WalFs.walDirIsI dir ic o, COMM Q o }> }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Repair)) (Val #lg)) (Val #dir))
  {{ (b : Bool), RET #b; osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm (callKey R r) 1 ∗
      (WalFs.walUnlockedTok ∨ ⌜b = false⌝) ∗ ∃ o : Option WalDur, Q o }}

/-- **`Repair(lg, dir)` while the last segment's lock is held** through another open file description
(2026-11-15, the lock semantics; `notes/wal-units/locks.md`, item 5; the user's decision of 2026-11-15: the
lock model as it is, a blocking lock may fail at any time): etcd's `openWALFromSnapshot` ignores a failed
`w.Close()` (whose sync failed before the locks were released) and calls `Repair`, whose `openLast` takes a
blocking `fileutil.LockFile` on the last segment. Its two outcomes are covered: it never returns while the
lock is held (any post holds), or it fails and `Repair` returns `false` (`openLast.specHeld`). With the
directory claim's share the failed handle holds (a path to `dir`, `osNames j (.except X)` at the
layout's names, the segments `segs` in name order, the last `gL`) and the held lock: `false`, nothing
changed, the share and the held lock kept. -/
abbrev wal.Repair.specHeld : Prop :=
  ∀ (lg : Loc) (R : Roots) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH)
    (segs : List SegG) (gL : SegG) (qd : Qp) (dqn : DFrac) (k : LockKind) (fd : w64),
  (∀ b ∈ X, walNameP b = false) → SegsNamed segs hj.cur → walInos hj.cur = segs.map (·.ino) →
  (segs.map (·.ino)).Nodup → (segs.map (·.name)).Pairwise (fun a b => go.GoStringLt a b) →
  (∀ g ∈ segs, ∃ sq ix : Nat, g.name = walFileName sq ix) → segs.getLast? = some gL →
  PathFits dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R dir (DFrac.own qd) j ∗
      osCallPerm (GF := GF) (callKey R dir) 1 ∗ osNames (GF := GF) j (.except X) dqn hj ∗
      osLock (GF := GF) k gL.ino fd ∗ fileutil.lockKind (GF := GF) k }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Repair)) (Val #lg)) (Val #dir))
  {{ (b : Bool), RET #b; ⌜b = false⌝ ∗ osPathS R dir (DFrac.own qd) j ∗ osCallPerm (callKey R dir) 1 ∗
      osNames j (.except X) dqn hj ∗ osLock k gL.ino fd }}

end spec

end EtcdGrove
end Perennial
