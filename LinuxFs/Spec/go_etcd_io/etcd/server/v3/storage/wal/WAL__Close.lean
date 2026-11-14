/-
`(*wal.WAL).Close()` of a WAL opened to append (S/wal.go:1053-1077) over `fsExt` (W10 of
`notes/wal-fsext-plan.md`): the main tree's axiom's first conjunct
(`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Close.lean`) with plan §3's binders (the area
`R jr r`, the handle `walOpenWF P Mr w dir`, the update at `walAuMask`) and §6 Q6's honest error arm.
`SpecPlan/`'s `Close` (the purge right consumed, the lock token back) is the same contract. Lean-first.
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

/-- **`w.Close()` of a WAL opened to append** (S/wal.go:1053-1077): closes the file pipeline, syncs
the tail (every record of the history: `walSyncedLb`), closes every lock's file and the directory's;
the handle's purge right is consumed (`walPurgeW`: `Close` unlocks every file, so the purge must have
stopped). The update commits after the sync, the state unchanged (the synced mark a lower bound);
then the WAL's files go back to the WAL invariant and the generation's lock token comes back
(`walUnlockedTok`: the next `Open` or `Create` may take it), with the whole call permission (the
handle's half and the pipeline's). *Error*: the sync failed (`Close` returns before it unlocks,
S/wal.go:1064-1066: the handle, its files and the token are lost, as `sync`'s error arm loses the
handle), or the directory's `Close` failed after everything else was done (then the success
resources come back too: the left disjunct holds whatever `err` is). Main tree's error arm:
`¬ storage.walCloseOk` (plan §6 Q6). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (Q : WalDur → IProp GF),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWF P Mr w dir ∗ WalFs.walPurgeW w dir ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir d, COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close"))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      (∃ d : WalDur, Q d ∗ WalFs.walSyncedLb dir d.H.length ∗ WalFs.walUnlockedTok ∗ osCallPerm 1) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
