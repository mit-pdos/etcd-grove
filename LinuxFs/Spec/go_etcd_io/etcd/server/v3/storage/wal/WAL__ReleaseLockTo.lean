/-
`w.ReleaseLockTo(a)` (S/wal.go:1009-1050) over `fsExt` (W9 of `notes/wal-fsext-plan.md`), the main
tree's axiom `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReleaseLockTo.lean` with plan §3's
binders (the area `R jr r`, the handle `walOpenWF P Mr w dir`, the update at `walAuMask`). Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

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

/-- **`w.ReleaseLockTo(a)`** (S/wal.go:1009-1050): unlocks the files before the lock just before the
first lock named `≥ a` (only the tail stays when none is) and closes them; with a synced snapshot
record of index `a` (at position `i < n`), the update raises the WAL's `unl` mark to
`walReleasePos H a` (the main tree's axiom: every record from there on stays in a locked file).
**`unl` is bookkeeping here** (plan §6 Q1, locks deferred: `fsExt` has no lock state, so nothing
reads the mark yet; the raise commits at the call's first step, right after `w.mu.Lock()`, whatever
the outcome, as the axiom's error arm already allowed, and `walInvBody_unl` takes any mark). An error
(a lock's file name `parseWALName` rejects, before any close) keeps the handle as well: nothing was
closed. The closed locks' fds go with them. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.spec (P : WalPbIn GF) (Mr : WalMarshal) :
    Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (a t : w64) (i n : Nat)
    (cs : ConfStateM) (Q : WalDur → IProp GF),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWF P Mr w dir ∗ WalFs.walSyncedLb dir n ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d ∗ ⌜d.H[i]? = some (WalOpG.snap ⟨cs, a, t⟩) ∧ i < n⌝ }>
        @ walAuMask, ∅
        <{ WalFs.walDiskAt dir { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) a) },
          COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
      go!"ReleaseLockTo")) (Val #a))
  {{ (err : GoInterface), RET #err; walOpenWF P Mr w dir ∗ ∃ d : WalDur, Q d }}

end spec

end EtcdGrove
end Perennial
