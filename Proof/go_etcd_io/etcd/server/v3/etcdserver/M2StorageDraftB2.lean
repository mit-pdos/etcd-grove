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

/-! ## The image's certificate with the sealed log's receipt (drafted: `InvImage.lean`) -/

/-- **Draft of `dbImage`**: today's text with the image's KV log's persistent receipt (the last
conjunct: the sender's sealed log's, `dbImageR_of_sender`). -/
def dbImageR (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageAt γk γ.raft.boot i (γ.pre ++ A) A D⌝ ∗
    ⧖ (mvcc.logCh (kvModel γk A)))

instance dbImageR_persistent (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data) :
    Persistent (dbImageR (GF := GF) γ γk i D) := by
  unfold dbImageR; infer_instance

/-- It is today's certificate and more. -/
theorem dbImageR_dbImage (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data) :
    dbImageR (GF := GF) γ γk i D ⊢ dbImage γ γk i D := by
  unfold dbImageR dbImage
  iintro ⟨%A, #HA, %h, -⟩
  iexists A
  iframe HA
  ipureintro; exact h

/-- `dbImageR` reads the KV names only through their start values (`dbImage_kv_congr`). -/
theorem dbImageR_kv_congr {γ : ServerRaftNames} {γk γk' : KVNames} {i : w64} {D : backend.Data}
    (h0 : γk.c0 = γk'.c0) (h1 : γk.ch0 = γk'.ch0) (h2 : γk.log0 = γk'.log0) :
    dbImageR (GF := GF) γ γk i D ⊢ dbImageR γ γk' i D := by
  have hk : ∀ A, kvModel γk A = kvModel γk' A := by
    intro A; simp only [kvModel, h0, h1, h2]
  iintro H
  iunfold dbImageR at H
  iunfold dbImageR
  icases H with ⟨%A, #Hlb, %h, #Hp⟩
  iexists A
  iframe Hlb
  rw [← hk]
  iframe Hp
  ipureintro
  refine ⟨h.1, ?_⟩
  have h2' := h.2
  unfold imageAt at h2' ⊢
  rw [← hk, ← h0]
  exact h2'

/-- **Draft of `srvImage`** (the network payload's `img`, `srvNet`; the snapshot directory's):
`dbImageR` at the fresh cluster's start, as today's. -/
def srvImageR (γ : SrvRaft) (i : w64) (D : backend.Data) : IProp GF :=
  iprop(∃ γk : KVNames, ⌜γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain false false false ∧
    γk.log0 = [[], []]⌝ ∗ dbImageR ⟨γ, [], W64 0⟩ γk i D)

instance srvImageR_persistent (γ : SrvRaft) (i : w64) (D : backend.Data) :
    Persistent (srvImageR (GF := GF) γ i D) := by
  unfold srvImageR; infer_instance

theorem srvImageR_srvImage (γ : SrvRaft) (i : w64) (D : backend.Data) :
    srvImageR (GF := GF) γ i D ⊢ srvImage γ i D := by
  unfold srvImageR srvImage
  iintro ⟨%γk, %h, #H⟩
  iexists γk
  ihave #H' := dbImageR_dbImage _ γk i D $$ H
  iframe H'
  ipureintro; exact h

/-- A member's certificate is the network's (`srvImage_of_dbImage`). -/
theorem srvImageR_of_dbImageR {γ : SrvRaft} {γk : KVNames} {i : w64} {D : backend.Data}
    (h0 : γk.c0 = W64 0) (h1 : γk.ch0 = apply.alarmChain false false false)
    (h2 : γk.log0 = [[], []]) :
    dbImageR (GF := GF) ⟨γ, [], W64 0⟩ γk i D ⊢ srvImageR γ i D := by
  iintro #H
  iunfold srvImageR
  iexists γk
  iframe H
  ipureintro
  exact ⟨h0, h1, h2⟩

/-- The network's certificate is any member's (`dbImage_of_srvImage`). -/
theorem dbImageR_of_srvImageR {γ : SrvRaft} {γk : KVNames} {i : w64} {D : backend.Data}
    (h0 : γk.c0 = W64 0) (h1 : γk.ch0 = apply.alarmChain false false false)
    (h2 : γk.log0 = [[], []]) :
    srvImageR (GF := GF) γ i D ⊢ dbImageR ⟨γ, [], W64 0⟩ γk i D := by
  iintro H
  iunfold srvImageR at H
  icases H with ⟨%γk', %h, #H⟩
  obtain ⟨h0', h1', h2'⟩ := h
  iapply (dbImageR_kv_congr (h0'.trans h0.symm) (h1'.trans h1.symm) (h2'.trans h2.symm)) $$ H

/-! ## The sender: its image's log is its sole writer's certified log -/

/-- **The sender's certificate** (what the `msgSnapC` branch, SNAPSHOT-SORRY #7, builds): today's
facts of `dbImage` (the committed `A`, the image at it) and the store's certified log at the image's
KV model with its receipt (the sole writer's `idxCert`, drafted to carry `⧖`: `idxCertR`; its log
is `kvModel γk A` by `kvApplied`). -/
theorem dbImageR_of_sender (γ : ServerRaftNames) (γk : KVNames) (γi : mvcc.IdxNames) (i : w64)
    (D : backend.Data) (A : List EntryModel) (log : mvcc.Log) (hlog : log = kvModel γk A)
    (h : uint.Z i = uint.Z γ.ai0 + A.length ∧ imageAt γk γ.raft.boot i (γ.pre ++ A) A D) :
    srvRLogLb (GF := GF) γ A ∗ mvcc.idxCertR γi log ⊢ dbImageR γ γk i D := by
  subst hlog
  iintro ⟨#HA, #Hc⟩
  iunfold mvcc.idxCertR at Hc
  icases Hc with ⟨-, #Hp⟩
  iunfold dbImageR
  iexists A
  iframe HA Hp
  ipureintro; exact h

/-! ## The installer: the restored log's receipt, from the image's certificate -/

/-- **The restored log's receipt** (glue): the image's certificate (`srvImageR`, what the snapshot
directory holds of the file the walk opens) and the image facts `snapRecv_image` derived from it
(`SnapImageFacts`: the committed `A'` of the image's length, `[[], []] ++ R = kvModel γr.kv A'`)
give `⧖ (logCh ([[], []] ++ R))`: two committed logs of one length are one log. -/
theorem rcpt_of_image (γ : SrvRaft) (γr : ReadNames) (d : mvcc.KBReal) (D : backend.Data) (cl : Loc)
    (i : w64) (A A' : List EntryModel) (x : apply.ApplyKV) (R : mvcc.Log)
    (memI : GMap w64 apply.MemberM)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain false false false) (hlog0 : γr.kv.log0 = [[], []])
    (hf : SnapImageFacts γr d D cl i A A' x R memI) :
    srvImageR (GF := GF) γ i D ∗ srvRLogLb γr.raft A' ⊢ ⧖ (mvcc.logCh ([[], []] ++ R)) := by
  have hlA : uint.Z i = A'.length := hf.len
  rw [hf.log, hraft]
  iintro ⟨#Himg, #HA'⟩
  ihave #Hdb : dbImageR ⟨γ, [], W64 0⟩ γr.kv i D $$ []
  · iapply (dbImageR_of_srvImageR hc0 hch hlog0); iexact Himg
  iunfold dbImageR at Hdb
  icases Hdb with ⟨%B, #HB, %hB, #Hp⟩
  ihave %Hcmp := srvRLogLb_prefix _ A' B $$ [HA' HB]
  · iframe HA' HB
  have hz : uint.Z (W64 0) = 0 := rfl
  have hlB : uint.Z i = B.length := by have := hB.1; simp only at this; omega
  have heq : A' = B := by
    rcases Hcmp with h | h
    · exact h.eq_of_length (by omega)
    · exact (h.eq_of_length (by omega)).symm
  subst heq
  iexact Hp

/-- **`Restore.specMR`'s premise for the walk's image** (`restoreRcptM`, either mode). -/
theorem restoreRcptM_of_image (γ : SrvRaft) (γr : ReadNames) (d : mvcc.KBReal) (D : backend.Data)
    (cl : Loc) (i : w64) (A A' : List EntryModel) (x : apply.ApplyKV) (R : mvcc.Log)
    (memI : GMap w64 apply.MemberM) (d' : mvcc.KBReal)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain false false false) (hlog0 : γr.kv.log0 = [[], []])
    (hf : SnapImageFacts γr d D cl i A A' x R memI) :
    srvImageR (GF := GF) γ i D ∗ srvRLogLb γr.raft A' ⊢ mvcc.restoreRcptM d' ([[], []] ++ R) := by
  iintro H
  ihave #Hp := rcpt_of_image γ γr d D cl i A A' x R memI hraft hc0 hch hlog0 hf $$ H
  unfold mvcc.restoreRcptM
  split
  · iexact Hp
  · itrivial

/-- **`restoreBoundM` by sealed logs** (in place of `restoreBoundM_of_chBound`, the configuration
bound's): today's pure premise of `Restore.specM`, for the walk's image, from its certificate. -/
theorem restoreBoundM_of_sealed (γ : SrvRaft) (γr : ReadNames) (d : mvcc.KBReal) (D : backend.Data)
    (cl : Loc) (i : w64) (A A' : List EntryModel) (x : apply.ApplyKV) (R : mvcc.Log)
    (memI : GMap w64 apply.MemberM) (d' : mvcc.KBReal)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain false false false) (hlog0 : γr.kv.log0 = [[], []])
    (hf : SnapImageFacts γr d D cl i A A' x R memI) :
    srvImageR (GF := GF) γ i D ∗ srvRLogLb γr.raft A' ⊢
      ⌜mvcc.restoreBoundM (GF := GF) d' ([[], []] ++ R)⌝ := by
  iintro H
  ihave #Hr := restoreRcptM_of_image γ γr d D cl i A A' x R memI d' hraft hc0 hch hlog0 hf $$ H
  iapply mvcc.restoreBoundM_of_rcpt $$ Hr

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
- `InvImage.lean`: `dbImage`, `srvImage` become `dbImageR`, `srvImageR` above (the receipt conjunct
  added; `dbImage_kv_congr`, `srvImage_of_dbImage`, `dbImage_of_srvImage` as proved above).
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
