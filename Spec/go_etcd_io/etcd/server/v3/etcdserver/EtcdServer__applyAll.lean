/-
`s.applyAll(ep, ap)` (`server.go`): the apply loop's step. Lean-first (no Rocq counterpart); the request path's unit 4b
(2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapTake
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NotifyC2
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.applyAll(ep, ap)`**, the apply loop's step on one `toApply` from raft (`ap`: its entries
`ms`, consecutive from `f0` with no gap after the applied index `ai`, as `applyEntries` takes them;
no snapshot, `rnApP`; its `notifyc`, a unit bag channel raft signals once it persisted the batch),
by the apply thread: `applySnapshot` (nothing: no snapshot), `applyEntries` (the KV goes from `x`
to `x'` by `entriesStep` over the entries above `ai`, under their shapes, `logShape`; the
applied index to `ai'`,
the last entry's or `ai`; each `setAppliedIndex` deposits the KV log after its entry, so the log
applied through `ai'` is `x'.log`; 2026-10-14, unit C2a: each entry committed,
`batchCommittedIdx`, and its log deposited ahead of its result), the backend's verification (`VerifyBackendConsistency`, the
trust boundary), the `proposalsApplied` gauge, **`applyWait.Trigger(ai')`** (with `appliedAtLeast γr
ai'`: the read loop's `ApplyWait` waiters through `ai'` are released once the KV has applied through
`ai'`), `<-ap.notifyc`, the snapshot trigger (`snapshotIfNeededAndCompactRaftLog`, over the
`snapshot`/`compactRaftLog` contracts), and a pending merged-snapshot request on `msgSnapC`
(names-only contracts). The apply thread's resources come back at `ai'`, with `loopOk`. **The
write budget** (the backend's unit 6, merged 2026-10-13): `applyEntries`' one write token of the
store per entry above `ai`, from the budget `srvWTPool E` (D19b, 2026-10-18; until then
`txn.storeWTs E.γ (unapplied ai ms).length`, handed in); (D22 J5, 2026-10-26) the count of tokens
taken from `w` to `w` plus the entries applied (`srvWTTaken`; until J5 at the applied index,
`srvWTAt γp ai`), with `uint.Z ai ≤ w` for the compaction's bound. **The KV model**
(2026-10-14, unit T1): as `applyEntries` (`kvApplied`, `kvBatch`). (D22 S-h, 2026-10-20, S-0's
amendment) The applied term: `ep.appliedt` the last applied entry's term, unchanged with none
(`termAfter`), which the merged snapshot's metadata carries. **The merged snapshot** (2026-10-31,
S1; until then the branch was dead, D22 S-h): a `MsgSnap` raft handed to `msgSnapC`
(`isServerApplyAll`'s bag, `rnSnapMsg`) of the batch's term `rt` (`apply.raftTerm`, `rnRtOk`) and
of a snapshot at most the applied index (the fork's guard, `notes/decisions.md`, "The merged
snapshot's index guard") is rewritten to carry the backend's image at the applied index
(`createMergedSnapshotMessage`) and sent (`sendMergedSnap`, over `isServerApplyAll`'s transport).
**The snapshot resources** (D22 J1b, 2026-10-31, the user's decision): what each snapshot install
takes and gives back (`srvSnapOwn`, `SnapRO.lean`) at the backend's environment, passed through
(no snapshot here: `E' = E`, the counter's bound raised to `ai'`), for J8a's snapshot case. -/
abbrev EtcdServer.applyAll.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (ep ap : Loc) (es : GoSlice)
    (ents : List Loc) (ms : List EntryModel) (f0 : w64) (rac nc : GoChan) (st : ApplyState)
    (ai at0 a t : w64) (cs : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (mst : Loc) (γs : MemStorNames) (γp : GName) (dv : Option Loc) (γnc : NotifyNames)
    (w : Nat) (nid : w64) (q : Qp) (γn : RNNames) (rt : w64) (n : Nat),
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShape (unapplied ai ms) →
  -- (D43 M3, 2026-10-25) the driver's view, `apply`'s
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (ai + 1) (unapplied ai ms) →
  -- (D22 J5, 2026-10-26) the applied index at most the write tokens taken (no snapshot installed;
  -- `snapshotIfNeededAndCompactRaftLog`'s)
  uint.Z ai ≤ w →
  -- (2026-10-31, the snapshot track: #11's S3) a fresh start's log: `A` the applied log through
  -- `ai`, `at0` its last term (the frozen terms' indices)
  uint.Z ai = A.length → lastTermIs A at0 →
  -- (2026-10-31, #11) what the snapshot takes (`snapshotIfNeededAndCompactRaftLog.spec`'s): the
  -- disk cooperating, the consistent index at least the applied one
  storage.diskOk → uint.Z ai ≤ uint.Z (ciEff γ st.k) →
  -- (2026-10-31, S1: the merged snapshot) the consistent index at most the applied one (so equal:
  -- the merged snapshot's image is exact at the applied index), the raft node's names those of the
  -- server's raft, and the batch's term good for a log at least the applied log after the batch
  uint.Z (ciEff γ st.k) ≤ uint.Z ai → γn.node = γr.raft.raft → (A ++ unapplied ai ms).length ≤ n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗ isServerApplyAll s γr ∗ batchWaitOk ρ E ms ∗
      taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      -- (D19i part 1) closed once raft advanced past the batch: (2026-10-30, the repair) the
      -- node `nid`'s applied index past it (`nodeAppliedLb`, `Compact`'s `J.B`; until then the
      -- storage's floor)
      rnAdvChan rac (letI := srvStor (GF := GF) ρ.raft.raft
        iprop(nodeAppliedLb ρ.raft.raft.cl nid
          (max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗ storDL ρ.raft.raft.cl nid
          (max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗
          -- (2026-10-30, the repair) the batch's entries frozen (`CreateSnapshot`'s)
          srvFrozenRange γs (uint.nat ai + 1)
            ((max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat + 1) ∗
          -- (2026-10-31, the snapshot track: #11's S3) with their terms
          srvFrozenTerms γs 1 (A ++ unapplied ai ms))) ∗ taSnapshotAddr ap ↦□ (null : Loc) ∗
      -- (D43 M3) `notifyc`: the receive deposits the view after the batch (`NotifyC.lean`)
      taNotifycAddr ap ↦□ nc ∗ isNotify γnc nc (dvView ρ.raft dv (A ++ unapplied ai ms)) ∗
      notifyRcv γnc ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗ epCsAt ρ.raft A cs ∗
      srvSnapState s ep mst γs ai (W64 0) ∗ applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗
      srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗ srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr ai ∗
      appliedLogAt γr ai x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗
      kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ srvApRes s γr A ∗
      -- (2026-10-30, the repair) with a view, the apply side's half of the running token
      (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      -- (2026-10-31, #11) what the snapshot takes: the disk snapshot's storage, the server's KV over
      -- the store, the storage's invariant at the node `nid`, the apply side's half of the WAL token
      srvSnapDisk s γr ∗ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗
      (letI : MemStorReg GF := ⟨γr.raft.raft.reg⟩; memStorInv mst γs γr.raft.raft.cl nid) ∗
      rnWalTok (srvRAddr s) q ∗
      -- (2026-10-31, S1) the batch's raft term `rt` (`apply.raftTerm`, the merge's guard), good for
      -- the log (`rnRtOk`: `0`, or a term committed through at least `n`)
      taRaftTermAddr ap ↦□ rt ∗ rnRtOk γn rt n ∗
      -- (D22 J1b, 2026-10-31; the user's decision) what each snapshot install takes and gives back
      -- (`srvSnapOwn`), passed through the batch
      srvSnapOwn s ci E γr ai }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #ep))
      (Val #ap))
  {{ RET #();
      -- (D22 receiver epochs, S7f, 2026-10-23) the apply thread's backend after the batch: the
      -- protocol's names `γ'` and the environment `E'` at some backend's (`beSucc`), with the
      -- server's view at them (`applySnapshot` moves the backend; without a snapshot they are
      -- `γ`, `TM`, `E`, `b`)
      ∃ (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (E' : apply.AEnv GF) (b' : GoInterface)
        (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        ⌜beSucc γ E γ' E'⌝ ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗ isServer s γ' ci TM' E' ρ γr ∗ srvApRes s γr (A ++ unapplied ai ms) ∗
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        epCsAt ρ.raft (A ++ unapplied ai ms) cs' ∗
        srvSnapState s ep mst γs ai' (W64 0) ∗ applyThread γ' st' ∗ applyBackend γ' ci b' ∗ ciApplying ci a' t' ∗
        srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗ srvAppliedOwn γr ai' ∗ appliedAtLeast γr ai' ∗
        srvWTTaken γp (w + (unapplied ai ms).length) ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E' ρ.wait x' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvApplied γr.raft γr.kv (A ++ unapplied ai ms) x' ∗ srvRest E' γr (A ++ unapplied ai ms)) ∗
        (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E'.s E'.γ) ∗ rnWalTok (srvRAddr s) q ∗
        -- (D22 J1b) the snapshot resources, at the batch's end
        srvSnapOwn s ci E' γr ai' ∗
        ⌜loopOk γ' st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          (ciEff γ' st'.k = ciEff γ st.k ∨
            uint.Z (ciEff γ' st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          -- (2026-10-31, the snapshot track: S1) the consistent index stays at least the applied one
          (uint.Z ai ≤ uint.Z (ciEff γ st.k) → uint.Z ai' ≤ uint.Z (ciEff γ' st'.k)) ∧
          -- (D22 S-h, 2026-10-20; S-0's amendment) the applied term: the last applied entry's
          termAfter at0 (unapplied ai ms) at'⌝ }}


/-- **`spec` in the auth mode `on`** (the auth plan's E3p, 2026-10-27): over `applyEntries.specOn`
and `snapshotIfNeededAndCompactRaftLog.spec` at auth on (the server with auth on, `logShapeOn`, the applier
row at the model's auth state `sa`, the apply thread at the mode-`on` model; the lessor finding no
lease, the receipts' bound); after the batch at the model's state after `A ++ unapplied ai ms` (its
auth state `sa'`). No snapshot is applied (`taSnapshotAddr ap ↦□ null`), so the backend stays. -/
abbrev EtcdServer.applyAll.specOn : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (ep ap : Loc) (es : GoSlice)
    (ents : List Loc) (ms : List EntryModel) (f0 : w64) (rac nc : GoChan) (st : ApplyState)
    (ai at0 a t : w64) (cs : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (mst : Loc) (γs : MemStorNames) (γp : GName) (dv : Option Loc) (γnc : NotifyNames)
    (w : Nat) (nid : w64) (γa : auth.AuthNames) (sa : auth.AuthState) (q : Qp) (γn : RNNames)
    (rt : w64) (n : Nat),
  E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 →
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShapeOn (unapplied ai ms) →
  -- (D43 M3, 2026-10-25) the driver's view, `apply`'s
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (ai + 1) (unapplied ai ms) →
  -- (D22 J5, 2026-10-26) the applied index at most the write tokens taken (no snapshot installed;
  -- `snapshotIfNeededAndCompactRaftLog`'s)
  uint.Z ai ≤ w →
  -- (2026-10-31, the snapshot track: #11's S3) a fresh start's log: `A` the applied log through
  -- `ai`, `at0` its last term (the frozen terms' indices)
  uint.Z ai = A.length → lastTermIs A at0 →
  -- (2026-10-31, #11) what the snapshot takes (`snapshotIfNeededAndCompactRaftLog.spec`'s): the
  -- disk cooperating, the consistent index at least the applied one
  storage.diskOk → uint.Z ai ≤ uint.Z (ciEff γ st.k) →
  -- (2026-10-31, S1: the merged snapshot) the consistent index at most the applied one (so equal:
  -- the merged snapshot's image is exact at the applied index), the raft node's names those of the
  -- server's raft, and the batch's term good for a log at least the applied log after the batch
  uint.Z (ciEff γ st.k) ≤ uint.Z ai → γn.node = γr.raft.raft → (A ++ unapplied ai ms).length ≤ n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM true s γ ci TM E ρ γr ∗ srvLessorNil s ∗ isServerApplyAll s γr ∗
      batchWaitOk ρ E ms ∗
      taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      -- (D19i part 1) closed once raft advanced past the batch: (2026-10-30, the repair) the
      -- node `nid`'s applied index past it (`nodeAppliedLb`, `Compact`'s `J.B`; until then the
      -- storage's floor)
      rnAdvChan rac (letI := srvStor (GF := GF) ρ.raft.raft
        iprop(nodeAppliedLb ρ.raft.raft.cl nid
          (max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗ storDL ρ.raft.raft.cl nid
          (max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗
          -- (2026-10-30, the repair) the batch's entries frozen (`CreateSnapshot`'s)
          srvFrozenRange γs (uint.nat ai + 1)
            ((max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat + 1) ∗
          -- (2026-10-31, the snapshot track: #11's S3) with their terms
          srvFrozenTerms γs 1 (A ++ unapplied ai ms))) ∗ taSnapshotAddr ap ↦□ (null : Loc) ∗
      -- (D43 M3) `notifyc`: the receive deposits the view after the batch (`NotifyC.lean`)
      taNotifycAddr ap ↦□ nc ∗ isNotify γnc nc (dvView ρ.raft dv (A ++ unapplied ai ms)) ∗
      notifyRcv γnc ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗ epCsAt ρ.raft A cs ∗
      srvSnapState s ep mst γs ai (W64 0) ∗ applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗
      srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗ srvApplyKVOn s E ρ.wait x sa ∗ srvAppliedOwn γr ai ∗
      appliedLogAt γr ai x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ srvApRes s γr A ∗
      -- (2026-10-30, the repair) with a view, the apply side's half of the running token
      (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
      srvTokRights E (ciEff γ st.k) ∗
      -- (2026-10-31, #11) what the snapshot takes: the disk snapshot's storage, the server's KV over
      -- the store, the storage's invariant at the node `nid`, the apply side's half of the WAL token
      srvSnapDisk s γr ∗ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗
      (letI : MemStorReg GF := ⟨γr.raft.raft.reg⟩; memStorInv mst γs γr.raft.raft.cl nid) ∗
      rnWalTok (srvRAddr s) q ∗
      -- (2026-10-31, S1) the batch's raft term `rt` (`apply.raftTerm`, the merge's guard), good for
      -- the log (`rnRtOk`: `0`, or a term committed through at least `n`)
      taRaftTermAddr ap ↦□ rt ∗ rnRtOk γn rt n ∗
      -- (D22 J1b, 2026-10-31; the user's decision) what each snapshot install takes and gives back
      -- (`srvSnapOwn`), passed through the batch
      srvSnapOwn s ci E γr ai }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #ep))
      (Val #ap))
  {{ RET #();
      -- (D22 receiver epochs, S7f, 2026-10-23) the apply thread's backend after the batch: the
      -- protocol's names `γ'` and the environment `E'` at some backend's (`beSucc`), with the
      -- server's view at them (`applySnapshot` moves the backend; without a snapshot they are
      -- `γ`, `TM`, `E`, `b`)
      ∃ (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (E' : apply.AEnv GF) (b' : GoInterface)
        (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        ⌜beSucc γ E γ' E'⌝ ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗ isServerM true s γ' ci TM' E' ρ γr ∗ srvApRes s γr (A ++ unapplied ai ms) ∗
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        epCsAt ρ.raft (A ++ unapplied ai ms) cs' ∗
        srvSnapState s ep mst γs ai' (W64 0) ∗ applyThread γ' st' ∗ srvTokRights E' (ciEff γ' st'.k) ∗
        applyBackend γ' ci b' ∗ ciApplying ci a' t' ∗
        srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗ srvAppliedOwn γr ai' ∗ appliedAtLeast γr ai' ∗
        srvWTTaken γp (w + (unapplied ai ms).length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVOn s E' ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' ∗
          srvRest E' γr (A ++ unapplied ai ms)) ∗
        (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E'.s E'.γ) ∗ rnWalTok (srvRAddr s) q ∗
        -- (D22 J1b) the snapshot resources, at the batch's end
        srvSnapOwn s ci E' γr ai' ∗
        ⌜loopOk γ' st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          (ciEff γ' st'.k = ciEff γ st.k ∨
            uint.Z (ciEff γ' st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          -- (2026-10-31, the snapshot track: S1) the consistent index stays at least the applied one
          (uint.Z ai ≤ uint.Z (ciEff γ st.k) → uint.Z ai' ≤ uint.Z (ciEff γ' st'.k)) ∧
          -- (D22 S-h, 2026-10-20; S-0's amendment) the applied term: the last applied entry's
          termAfter at0 (unapplied ai ms) at'⌝ }}

/-- **`s.applyAll(ep, ap)` on a snapshot payload** (2026-11-01, J8a-5, step 5e; `rnApSnap`'s:
`notes/snapshot-j8a-plan.md`, item 4), by the apply thread of a fresh cluster's member (the start
values of `NewServer.spec`: `γr.raft` the raft names with no prefix, the KV's start, compaction off):
the snapshot `sv` at the index `i` past the applied index `ai` (below `2^61`, at least the boot
log), certified (`snapshotCert`), in the member's snapshot directory (`nodeSnapLocal`, the member
`nid` the server's), with no entries, its two-receive `notifyc` and `raftAdvancedC` (the node's
applied index at `i`, the storage's snapshot frozen there). `applySnapshot` installs it
(`applySnapshot.specSnap`, over the snapshot path's resources `srvSnapOwn` and the apply thread's
`srvApRes`), `applyEntries` returns at once, `applyWait.Trigger(i)` releases the waiters through
`i` (`applied_jump`), the two receives, `snapshotIfNeededAndCompactRaftLog` does nothing (disk =
memory = applied index), and a pending merged-snapshot request is served at `i`. After: `applyAll.spec`'s
post shape at the snapshot's backend (`beSucc`), the applied log the image's `A'` (committed,
`pre ++ A'` of length `i`, extending `A`; J8b ties it to raft's `cum`), the applied index and term
the snapshot's, the consistent index at `i`, `ep.confState` the snapshot's (the voters'), no write
token taken. Not here: the driver's view (`dv`; the caller frames its running token). -/
abbrev EtcdServer.applyAll.specSnap : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (ep ap : Loc) (es : GoSlice) (sn : Loc)
    (sv : SnapshotM) (rac nc : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (A : List EntryModel) (mst : Loc) (γs : MemStorNames) (γp : GName)
    (γnc : NotifyNames) (w : Nat) (nid : w64) (q : Qp) (γn : RNNames) (rt : w64) (n : Nat),
  -- the snapshot past the applied index, below `2^61`, at least the boot log
  uint.Z ai < uint.Z sv.Metadata'.Index' → uint.Z sv.Metadata'.Index' < 2 ^ 61 →
  (γr.raft.raft.boot.length : Int) ≤ uint.Z sv.Metadata'.Index' →
  -- the applied log `A` through `ai`, the consistent index at most the applied one
  uint.Z ai = A.length → uint.Z (ciEff γ st.k) ≤ uint.Z ai →
  -- a fresh cluster's start (`snapRecv_image`'s), compaction off
  γr.raft = ⟨γr.raft.raft, [], W64 0⟩ → γr.kv.c0 = W64 0 →
  γr.kv.ch0 = apply.alarmChain false false false → γr.kv.log0 = [[], []] → E.cmp = false →
  -- the batch's term good for a log at least the snapshot's (the merge's guard)
  γn.node = γr.raft.raft → uint.nat sv.Metadata'.Index' ≤ n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗ isServerApplyAll s γr ∗ srvMemberIDAddr s ↦□ nid ∗
      -- the payload (`rnApSnap`'s)
      taEntriesAddr ap ↦□ es ∗ es ↦*□ ([] : List Loc) ∗
      taSnapshotAddr ap ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
      (letI := srvStor (GF := GF) γr.raft.raft; iprop(snapshotCert γr.raft.raft.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
        nodeSnapLocal γr.raft.raft.cl nid sv.Metadata'.Index')) ∗
      taNotifycAddr ap ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
      taRaftAdvancedCAddr ap ↦□ rac ∗
      rnAdvChan rac (letI := srvStor (GF := GF) ρ.raft.raft
        iprop(nodeAppliedLb ρ.raft.raft.cl nid (uint.nat sv.Metadata'.Index') ∗
          storDL ρ.raft.raft.cl nid (uint.nat sv.Metadata'.Index') ∗
          srvFrozenAt γs (uint.nat sv.Metadata'.Index') ∗
          srvFrozenBelow γs (uint.nat sv.Metadata'.Index'))) ∗
      taRaftTermAddr ap ↦□ rt ∗ rnRtOk γn rt n ∗
      -- the apply thread's resources, as `spec`'s
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      srvSnapState s ep mst γs ai (W64 0) ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗
      srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      srvWTPool E γp ∗ srvWTTaken γp w ∗ kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗
      srvApRes s γr A ∗ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗
      rnWalTok (srvRAddr s) q ∗
      -- the snapshot path's resources (`srvSnapRO`'s configuration rebuild over
      -- `isServerApplyAll`'s two fields)
      srvSnapOwn s ci E γr ai ∗
      -- (J8a-4's, 2026-11-01) `applySnapshot.specSnap`'s meta reads of the backend it opens, at
      -- the apply names `γ` (`bootOk`'s `#HmetaSnap`, which `run` carries)
      □ (∀ (π : ApplyPhys) (γB : backend.BNames) (P : backend.BParams) (D : backend.Data),
        ⌜ciKeys P ∧ metaIs D π.m0 ∧ π.bwb = γB.wb ∧ π.bopn = γB.opn⌝ -∗
        backend.hkOwn γB (backend.hkData P D) -∗ backend.bFresh γB -∗
        backend.hkOwn γB (backend.hkData P D) ∗ backend.bFresh γB ∗
        □ ∀ (W : IProp GF) (b : Loc),
          backend.isBackend γB P W (batchLockInv (γ.withPh π) (metaTM γB P)) b -∗
          isMetaBackend (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) (⊤ \ ↑applyN)
            (readView (γ.withPh π))) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #ep))
      (Val #ap))
  {{ RET #();
      ∃ (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (E' : apply.AEnv GF) (b' : GoInterface)
        (st' : ApplyState) (A' : List EntryModel) (cs' : Loc),
        ⌜beSucc γ E γ' E'⌝ ∗ isServer s γ' ci TM' E' ρ γr ∗ srvApRes s γr A' ∗
        srvRLogLb γr.raft A' ∗
        epAppliedIAddr ep ↦ sv.Metadata'.Index' ∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' ∗
        epConfState ep cs' ∗ epCsAt ρ.raft A' cs' ∗
        srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) ∗ applyThread γ' st' ∗
        applyBackend γ' ci b' ∗ ciApplying ci a t ∗
        srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗
        srvAppliedOwn γr sv.Metadata'.Index' ∗ appliedAtLeast γr sv.Metadata'.Index' ∗
        srvWTTaken γp w ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E' ρ.wait x' ∗
          appliedLogAt γr sv.Metadata'.Index' x'.log ∗
          kvApplied γr.raft γr.kv A' x' ∗ srvRest E' γr A') ∗
        (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E'.s E'.γ) ∗ rnWalTok (srvRAddr s) q ∗
        srvSnapOwn s ci E' γr sv.Metadata'.Index' ∗
        ⌜loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' ∧
          A <+: A' ∧ (γr.raft.pre ++ A').length = uint.nat sv.Metadata'.Index' ∧
          lastTermIs A' sv.Metadata'.Term'⌝ }}

end spec

end EtcdGrove
end Perennial
