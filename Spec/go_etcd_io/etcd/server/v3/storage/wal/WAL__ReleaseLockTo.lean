/-
`(*wal.WAL).ReleaseLockTo` (WAL W4a, 2026-11-11, revised after the Freeze review and its second and third rounds, and in W4a.1 and its revision 1 (2026-11-12, findings F-W4b-1/F-W4b-2 and the delta review's B1/M1/M2, decided by etcd-grove-81), and in W4a.2 (2026-11-12: the purge bounds' completeness, R1/R2, the soundness findings F-W4a2-1/F-W4a2-2, logically atomic restatements, decided by etcd-grove-81; the fork fix `1aaca041c` approved by the user) the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `1aaca041c` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names (`Proof/go_etcd_io/etcd/server/v3/storage/WalBodies.lean` gives the bodies of the posts that name a past state). `walDiskAt`'s synced mark and `named` are lower bounds of the real ones (W4a.1 revision 1, `GooseLang/Ext/AbsDisk/Specs.lean`).
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

/-- **`w.ReleaseLockTo(a)`** (S/wal.go:984-1026): keeps locked the files from the lock just before
the first lock named `≥ a` (only the tail when none is), and unlocks the earlier ones. With a synced
snapshot record of index `a`, every record from `walReleasePos H a` on stays in a locked file
(`unl`): the smaller of the guard's position (the snapshot record's last position when every later
cut names its file above `a`, `walRelGuard`; else the history's length; `walGuardPos`) and the name
bound (the last position a file named below `a` can start at, `walNameBound … true`: a file starts at
a `walCutPos` and is named `w.enti + 1`, and `walLastEntIdx` of the prefix bounds `w.enti` from below
across restarts, since a successful write-mode `ReadAll` matched its start record, the fork's
`1aaca041c`, and no index wraps). WAL W4a.2 (R1): the name bound is new; the guard gains clause 4
(no index `2^64-1`; finding F-W4a2-1: Go test `w4a2-tests` `TestW4a2NameWrapReleaseLockTo`, where the
wrapped name lets `ReleaseLockTo` unlock the file holding the snapshot record). Go evidence: the W4a.2
probe (every `ReleaseLockTo` of the WAL tester across restarts, the first locked file's position at
or below the bound) and `w4a2-tests` `TestW4a2NameBoundBoundary`. Logically atomic (WAL W4a.2, the W4c gate of W4a.1 revision 1, M-R1): W4c's restart runs under the
crash model, so the tester keeps the WAL in an invariant and finds it there at a crash during the
call; the post's `Q` is of the accessed state. The body commits at its
unlocking (the step `"WalUnlock"` of the bound); an error (a file name it cannot parse, before any
unlock) commits the same raise, which only allows more purging. -/
abbrev wal.WAL.ReleaseLockTo.spec : Prop :=
  ∀ (w : Loc) (dir : GoString) (a t : w64) (i n : Nat) (cs : ConfStateM) (Q : WalDur → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walOpenW w dir ∗ walSyncedLb dir n ∗
      AU <{ ∃∃ d : WalDur, walDiskAt dir d ∗ ⌜d.H[i]? = some (WalOpG.snap ⟨cs, a, t⟩) ∧ i < n⌝ }> @ ⊤, ∅
        <{ walDiskAt dir { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) a) }, COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"ReleaseLockTo")) (Val #a))
  {{ (err : GoInterface), RET #err; walOpenW w dir ∗ ∃ d : WalDur, Q d }}

end spec

end EtcdGrove
end Perennial
