/-
`wal.Repair` (WAL W4a, 2026-11-11, revised after the Freeze review and its second and third rounds, and in W4a.1 and its revision 1 (2026-11-12, findings F-W4b-1/F-W4b-2 and the delta review's B1/M1/M2, decided by etcd-grove-81), and in W4a.2 (2026-11-12: the purge bounds' completeness, R1/R2, the soundness findings F-W4a2-1/F-W4a2-2, logically atomic restatements, decided by etcd-grove-81; the fork fixes `1aaca041c` and `0b50f0426` approved by the user) the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `0b50f0426` (S/ = `server/storage/wal/`, line numbers of `c90b03b56`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names (`Proof/go_etcd_io/etcd/server/v3/storage/WalBodies.lean` gives the bodies of the posts that name a past state). `walDiskAt`'s synced mark and `named` are lower bounds of the real ones (W4a.1 revision 1, `GooseLang/Ext/AbsDisk/Specs.lean`).
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
`walDirIs`, releases it), then acts as with no handle; no other WAL call intervenes, since `Repair`'s
atomic update holds the whole map (`walDirIs`) for its caller's invariant. Go test `rev3-tests`
`TestReview3RepairLive` (with `Create`'s or an opening handle live, `Repair` does not return within
2s; after `Close` it completes). Logically atomic (WAL W4a.2, the W4c gate of W4a.1 revision 1, M-R1): W4c's restart runs under the
crash model, so the tester keeps the WAL in an invariant and finds it there at a crash during the
call; the post's `Q` is of the accessed state. The body linearizes at its truncation (no step:
the model's state, which holds no torn record, is unchanged). -/
abbrev wal.Repair.spec : Prop :=
  ∀ (lg : Loc) (r dir : GoString) (Q : Option WalDur → IProp GF), walAreaDir r dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗ walAreaOk r ∗
      AU <{ ∃∃ o : Option WalDur, walDirIs dir o }> @ ⊤, ∅ <{ walDirIs dir o, COMM Q o }> }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Repair)) (Val #lg)) (Val #dir))
  {{ (b : Bool), RET #b; ∃ o : Option WalDur, Q o }}

end spec

end EtcdGrove
end Perennial
