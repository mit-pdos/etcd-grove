/-
**M2, the storage side: B2 by sealed logs (Draft)** (`notes/m2-storage-plan.md`, "B2 by sealed logs";
the user's decision of 2026-10-30, after the restore chain's round 2: no `NewServer` premise, every
installed snapshot's log is some member's sealed log, carried with the snapshot). Imported by nothing;
no `axiom`, no `sorry`; the snapshot track's statements (the collaborator's) and the trusted
`NewServer`'s are drafted here, not switched. Supersedes the drafts of a configuration bound
(`srvChBound` at `NewServer.specCompact`, round 5) and of the user's `Nc`/`K` form (`srvLogLe`,
`kvChLe`, `srvPutLe`: the pure entry bound is false of etcd, the plan's "Task 5"), dropped.

**Where the image is made and how it travels.** etcd's raft snapshot carries no data (`snapshot()`:
`CreateSnapshot` with `d = nil`; raft's registry `ownSnapsMade` in `srvClusterOk` has no KV content;
`srvSnapStor` is raft's log only). The KV image is made when a leader sends a `MsgSnap`
(`createMergedSnapshotMessage`: `s.KV().Commit()`, then `s.be.Snapshot()`, the apply thread's
`msgSnapC` branch, SNAPSHOT-SORRY #7), and it travels with its certificate `srvImage i D` (the
network payload's `img`, `srvNet`), which the receiver's transport keeps in the snapshot directory
(`snapDirInv ss γd (srvImage …) …`) and the receiver reads (`snapRecv_image`: `SnapImageFacts`,
`[[], []] ++ R = kvModel γr.kv A'`). So the certificate is the carrier, not the registry and not
`snapshot()`'s post (neither changes).

**The carried fact** (`dbImageR`, `srvImageR`): the image's KV log has a persistent time receipt,
`⧖ (logCh (kvModel γk A))` (Perennial's `preceipt`: at least that many counted steps of the one
global counter, shared by every member: one Iris instance, one `receiptBound GF`). The sender has
it: its image's log is its sole writer's certified log (`kvApplied`: `x.log = kvModel γk A`;
`txn.soleWriter`'s `idxCert`), and a certified log carries its receipt (the mvcc Draft's
`idxCertR`, from the writer's own `⧗` at the commit, `idxWriter_commitR`). The installer gets
`restoreRcptM` for the restored log (`restoreRcptM_of_image`), hence today's pure `restoreBoundM`
(`restoreBoundM_of_sealed`), with no configuration bound.

**The induction closes** (the mvcc Draft, `storage/mvcc/M2StorageDraftSealed.lean`): the restored
writer's handle is `idxWriterP` (`⧖` in place of `⧗`; `idxWriterP_of_image` from the image's
receipt), each change raises the receipt by the Go step that puts it (`treeIndex.Put.specP`,
`treeIndex.Tombstone.specP`, proved), and its commit certifies the log with its receipt again
(`idxWriterP_commit`: `idxCertR`), which is what the sender's lemma here takes
(`dbImageR_of_sender`): the next member restoring this one's later image gets its bound the same way.
Exclusive receipts could not do this (the image's `⧗` are the sender's writer's); persistent ones
can, because a step raises `⧖ m` to `⧖ (m + 1)` whoever holds it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvFacts
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftSealed

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/- (#7-cmp's Freeze, 2026-11-02, the user's approval: `dbImageR`/`srvImageR` retired. `dbImage` carries
the receipt in place (`InvImage.lean`), the sender's from the sole writer's `idxCert` (`merged_image`),
the installer's `restoreRcptM` from it (`SnapRecvFacts.image_restoreRes`, in `snapRecv_image`); with
them went `dbImageR_of_sender`, `rcpt_of_image`, `restoreRcptM_of_image`, `restoreBoundM_of_sealed`.) -/

/-- **The seal bound after a compacted restore** (in place of `srvChBound_small`): the restored
writer's later seals are bounded by its own persistent receipt (`idxWriterP_seal`'s `idxSealedR`),
and so, under `NewServer`'s `receiptBound GF ≤ 2 ^ 48`, below `2 ^ 48` (`txn.soleWriter_small'`'s
conclusion), with no premise. -/
theorem sealedR_small (γi : mvcc.IdxNames) (log : mvcc.Log) (hrb : receiptBound GF ≤ 2 ^ 48) :
    mvcc.idxSealedR (GF := GF) γi log ⊢
      ⌜mvcc.logCh log < receiptBound GF ∧ mvcc.logCh log < 2 ^ 48⌝ := by
  iintro #H
  ihave %h := mvcc.idxSealedR_small γi log $$ H
  ipureintro; exact ⟨h, by omega⟩

/-! ## The drafted statement changes (exact texts; for the collaborator and the user)

**Snapshot track** (the collaborator's):
- `InvImage.lean`: `dbImage` carries the receipt (landed in place at #7-cmp's Freeze, 2026-11-02;
  `dbImageR`/`srvImageR` retired).
- `InvBuild.lean`, `srvNet`: `img := fun i D => srvImage γ i D` stays textually (`srvImage` is the
  drafted one).
- `SnapRO.lean` and the snapshot directory's other mentions: `inv snapDirN (snapDirInv ss γd
  (srvImage γr.raft.raft) (srvSnapRm γt γr))` stays textually.
- The sender (`applyAll`'s `msgSnapC` branch, SNAPSHOT-SORRY #7): builds `srvImage` by
  `dbImageR_of_sender` from `txn.soleWriter`'s certificate at `x.log = kvModel γk A`.
- The receiver (`snapRecv_image`, SNAPSHOT-SORRY #7/#8's snapshot batch): unchanged but for
  `dbImage_of_srvImage`; the walk's caller adds `restoreRcptM_of_image`.
- `EtcdServer.applySnapshot.specSnap`: when `hcm : d.cm = false` goes (items 15/16), its pre gains

      mvcc.restoreRcptM d ([[], []] ++ R) ∗

  (the new backend's mode is `d.cm`: `Restore.specMR`'s `d'.cm = d.cm`), which the walk passes to
  `watchableStore.Restore`/`store.Restore` (`specMR`). While `hcm` stays it is `True`.
- `EtcdServer.snapshot` (`SnapTakeProof`), `srvSnapStor`, `srvSnapFrozen`, `snapTakenLb`,
  `srvClusterOk`'s registry `ownSnapsMade`: **unchanged** (raft's snapshot has no KV content).

**mvcc** (internal; `storage/mvcc/M2StorageDraftSealed.lean`): `idxSealed`'s and `idxCert`'s
`⌜logCh log < receiptBound GF⌝` become `⧖ (logCh log)` (`idxSealedR`, `idxCertR`); the writer's
handle `idxWriterP` (by the mode or always); `treeIndex.Put.spec`/`Tombstone.spec` at it
(`specP`); `store.Restore.specM`'s `restoreBoundM` premise becomes the pre's `restoreRcptM`
(`specMR`, `specMR_of_specM`).

**`NewServer`** (trusted): **no change** (`specCompact` keeps `receiptBound GF ≤ 2 ^ 48`; the
drafted `srvChBound`/`Nc`/`K` premises are dropped). -/

end draft

end EtcdGrove
end Perennial
