/-
`wal.Repair` (WAL W4a, 2026-11-11, revised after the Freeze review and its second and third rounds; the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names (`Proof/go_etcd_io/etcd/server/v3/storage/WalBodies.lean` gives the bodies of the posts that name a past state). `walDiskAt`'s synced mark and `named` are lower bounds of the real ones (W4a.1 revision 1, `GooseLang/Ext/AbsDisk/Specs.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Spec.go_uber_org.zap.Defs
public import Proof.go_etcd_io.raft.v3.InvPbLog
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [walpb_sem : go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- **`Repair(lg, dir)`** (S/repair.go:32-106): truncates a torn last record and fsyncs; the decoded
records are unchanged (a synced record is never torn: the sector assumption). With no WAL at `dir`
(`o = none`) it returns false (`readWALNames`). It takes the tail file's lock blocking (`LockFile`,
S/repair.go:30-38, 120-127): while a handle holds it, `Repair` blocks until none does (a
concurrent `Close` of the handle, e.g. of an opening or failed one, whose `Close` needs no
`walDirIs`, releases it), then acts as with no handle; no other WAL call intervenes, since `Repair`
holds the whole map (`walDirIs`). Go test `rev3-tests` `TestReview3RepairLive` (with `Create`'s or
an opening handle live, `Repair` does not return within 2s; after `Close` it completes). -/
abbrev wal.Repair.spec : Prop :=
  ∀ (lg : Loc) (r dir : GoString) (o : Option WalDur), walAreaDir r dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗ walAreaOk r ∗ walDirIs dir o }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Repair)) (Val #lg)) (Val #dir))
  {{ (b : Bool), RET #b; walDirIs dir o }}

end spec

end EtcdGrove
end Perennial
