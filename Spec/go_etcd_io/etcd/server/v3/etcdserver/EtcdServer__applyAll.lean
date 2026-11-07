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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthCompRows

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

/-- **`s.applyAll(ep, ap)` on a batch of entries** (the auth component's stage 2, 2026-11-04: one
statement in both auth modes, over the component `C`, the environment's; until then `specBatch`
with auth off, now `specBatchOff`, and `specOn` with auth on, both `ModeSpecs.lean`'s corollaries):
`specBatchOff`'s contract (see there) with the server's view, the applier row and the model in the
component (`isServerC`, `srvApplyKVC` at the model's auth state `sa`, `kvAppliedM C.isOn`), the
entries' shapes in the mode (`logShapeM`), the lessor finding no lease with auth on (`acLessor`), the
rights to issue tokens at the consistent index (`acTok`) and the receipts' bound. -/
abbrev EtcdServer.applyAll.specBatch : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (C : AuthC) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (ep ap : Loc) (es : GoSlice)
    (ents : List Loc) (ms : List EntryModel) (f0 : w64) (rac nc : GoChan) (st : ApplyState)
    (ai at0 a t : w64) (cs : Loc) (x : apply.ApplyKV) (sa : auth.AuthState) (A : List EntryModel)
    (mst : Loc) (γs : MemStorNames) (γp : WTNames) (dv : Option Loc) (γnc : NotifyNames)
    (w : Nat) (nk : GName) (q : Qp) (γn : RNNames) (rt : w64) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      -- the component the environment's, and the batch's premises (`specBatchOff`'s, the shapes in
      -- the mode, `logShapeM`)
      -- (strict M1, 2026-11-06; merge of `lean`) the receipts' bound in both modes, in place of
      -- `acReceiptOk C` (`applyEntries`': the log's smallness comes from the writer's receipt,
      -- `srvApplyKV_small`)
      ⌜E.authMode = C.mode ∧ receiptBound GF ≤ 2 ^ 48 ∧
        (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) ∧ uint.Z ai + 1 < 2 ^ 64 ∧
        loopOk γ st ai ∧ logShapeM C.isOn E.lm (unapplied ai ms) ∧
        dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (ai + 1) (unapplied ai ms) ∧
        uint.Z ai = A.length ∧ lastTermIs A at0 ∧
        storage.diskOk ∧ uint.Z ai ≤ uint.Z (ciEff γ st.k) ∧
        uint.Z (ciEff γ st.k) ≤ uint.Z ai ∧ γn.node = γr.raft.raft ∧ γr.raft.pre = [] ∧
        (A ++ unapplied ai ms).length ≤ n⌝ ∗
      isServerC C s γ ci TM E ρ γr ∗ acLessor C s ∗ isServerApplyAll s γr ∗ batchWaitOk ρ E ms ∗
      taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      -- (D19i part 1) closed once raft advanced past the batch: (2026-10-30, the repair) the
      -- the node's (on the storage of key `nk`) applied index past it (`nodeAppliedLb`, `Compact`'s `J.B`; until then the
      -- storage's floor)
      rnAdvChan rac (letI := srvStor (GF := GF) ρ.raft.raft
        iprop(nodeAppliedLb ρ.raft.raft.cl nk
          (max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗ nodeCommitLb ρ.raft.raft.cl nk
          (max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗
          -- (2026-10-30, the repair) the batch's entries frozen (`CreateSnapshot`'s)
          srvFrozenRange γs (uint.nat ai + 1)
            ((max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat + 1) ∗
          -- (2026-10-31, the snapshot track: #11's S3) with their terms
          srvFrozenTerms γs 1 (A ++ unapplied ai ms) ∗
          -- (2026-11-03, R2b-1 stage 5) the batch's log handed at its WAL `Save`
          rnWalHanded γn (max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat)) ∗
          taSnapshotAddr ap ↦□ (null : Loc) ∗
      -- (D43 M3) `notifyc`: the receive deposits the view after the batch (`NotifyC.lean`)
      taNotifycAddr ap ↦□ nc ∗ isNotify γnc nc (dvView ρ.raft dv (A ++ unapplied ai ms)) ∗
      notifyRcv γnc ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗ epCsAt ρ.raft A cs ∗
      srvSnapState s ep mst γs ai (W64 0) ∗ applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗
      srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvBemuReaderAt s E.γbe ∗ srvApplyKVC C s E ρ.wait x sa ∗ srvAppliedOwn γr ai ∗
      appliedLogAt γr ai x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp.cnt w ∗
      kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ srvApRes s γr A ∗
      -- (2026-10-30, the repair) with a view, the apply side's half of the running token
      (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      -- (2026-10-31, #11) what the snapshot takes: the disk snapshot's storage, the server's KV over
      -- the store, the storage's invariant at the storage key `nk`, the apply side's half of the WAL token
      srvSnapDisk s γr ∗ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ □ mvcc.api.isMvcc kv E.γ ∗ ⌜kv = E.kv⌝) ∗
      (letI : MemStorReg GF := ⟨γr.raft.raft.reg⟩; memStorInv mst γs γr.raft.raft.cl nk) ∗
      rnWalTokA γn (srvRAddr s) q ∗
      -- (2026-10-31, S1) the batch's raft term `rt` (`apply.raftTerm`, the merge's guard), good for
      -- the log (`rnRtOk`: `0`, or a term committed through at least `n`)
      taRaftTermAddr ap ↦□ rt ∗ rnRtOk γn rt n ∗
      -- (D22 J1b, 2026-10-31; the user's decision) what each snapshot install takes and gives back
      -- (`srvSnapOwn`), passed through the batch
      srvSnapOwn s ci E γr γ ai ∗
      -- the rights to issue tokens at the consistent index
      acTok C (ciEff γ st.k) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #ep))
      (Val #ap))
  {{ RET #();
      -- (D22 receiver epochs, S7f, 2026-10-23) the apply thread's backend after the batch: the
      -- protocol's names `γ'` and the environment `E'` at some backend's (`beSucc`), with the
      -- server's view at them (`applySnapshot` moves the backend; without a snapshot they are
      -- `γ`, `TM`, `E`, `b`)
      ∃ (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (E' : apply.AEnv GF) (b' : GoInterface)
        (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        ⌜beSucc γ E γ' E'⌝ ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗ isServerC C s γ' ci TM' E' ρ γr ∗ acLessor C s ∗ srvApRes s γr (A ++ unapplied ai ms) ∗
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        epCsAt ρ.raft (A ++ unapplied ai ms) cs' ∗
        srvSnapState s ep mst γs ai' (W64 0) ∗ applyThread γ' st' ∗ acTok C (ciEff γ' st'.k) ∗ applyBackend γ' ci b' ∗ ciApplying ci a' t' ∗
        srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E'.γ 1 ∗ srvBemuReaderAt s E.γbe ∗ srvAppliedOwn γr ai' ∗ appliedAtLeast γr ai' ∗
        srvWTTaken γp.cnt (w + (unapplied ai ms).length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVC C s E' ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' ∗ srvRest E' γr (A ++ unapplied ai ms)) ∗
        (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ □ mvcc.api.isMvcc kv E'.γ ∗ ⌜kv = E'.kv⌝) ∗ rnWalTokA γn (srvRAddr s) q ∗
        -- (D22 J1b) the snapshot resources, at the batch's end
        srvSnapOwn s ci E' γr γ' ai' ∗
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
values of `NewServer.spec`: `γr.raft` the raft names with no prefix, the KV's start; either compaction
mode since M2's item 15, stage C; strict M1, 2026-11-06, over the API):
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
    (x : apply.ApplyKV) (A : List EntryModel) (mst : Loc) (γs : MemStorNames) (γp : WTNames)
    (γnc : NotifyNames) (w : Nat) (nid : w64) (nk : GName) (q : Qp) (γn : RNNames) (rt : w64) (n : Nat),
  -- the snapshot past the applied index, below `2^61`, at least the boot log
  uint.Z ai < uint.Z sv.Metadata'.Index' → uint.Z sv.Metadata'.Index' < 2 ^ 61 →
  (γr.raft.raft.boot.length : Int) ≤ uint.Z sv.Metadata'.Index' →
  -- the applied log `A` through `ai`, the consistent index at most the applied one
  uint.Z ai = A.length → uint.Z (ciEff γ st.k) ≤ uint.Z ai →
  -- a fresh cluster's start (`snapRecv_image`'s), in either compaction mode (M2's item 15, stage C;
  -- until then `E.cmp = false`)
  γr.raft = ⟨γr.raft.raft, [], W64 0⟩ → γr.kv.c0 = W64 0 →
  γr.kv.ch0 = apply.alarmChain false false false → γr.kv.log0 = [[], []] →
  -- (until the lease-expiry plan's S2–S4, 2026-11-05, also `γr.kv.lg = false`: a cluster that
  -- grants no lease, the lease-grant plan's D2 interim restriction)
  -- the batch's term good for a log at least the snapshot's (the merge's guard)
  γn.node = γr.raft.raft → γr.raft.pre = [] → uint.nat sv.Metadata'.Index' ≤ n →
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
        iprop(nodeAppliedLb ρ.raft.raft.cl nk (uint.nat sv.Metadata'.Index') ∗
          nodeCommitLb ρ.raft.raft.cl nk (uint.nat sv.Metadata'.Index') ∗
          srvFrozenAt γs (uint.nat sv.Metadata'.Index') ∗
          srvFrozenBelow γs (uint.nat sv.Metadata'.Index') ∗
          rnWalHanded γn (uint.nat sv.Metadata'.Index'))) ∗
      taRaftTermAddr ap ↦□ rt ∗ rnRtOk γn rt n ∗
      -- the apply thread's resources, as `spec`'s
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      srvSnapState s ep mst γs ai (W64 0) ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvBemuReaderAt s E.γbe ∗
      srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      srvWTPool E γp ∗ srvWTTaken γp.cnt w ∗ kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗
      srvApRes s γr A ∗ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ □ mvcc.api.isMvcc kv E.γ ∗ ⌜kv = E.kv⌝) ∗
      rnWalTokA γn (srvRAddr s) q ∗
      -- the snapshot path's resources (`srvSnapRO`'s configuration rebuild over
      -- `isServerApplyAll`'s two fields)
      srvSnapOwn s ci E γr γ ai ∗
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
        srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E'.γ 1 ∗ srvBemuReaderAt s E.γbe ∗
        srvAppliedOwn γr sv.Metadata'.Index' ∗ appliedAtLeast γr sv.Metadata'.Index' ∗
        srvWTTaken γp.cnt w ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E' ρ.wait x' ∗
          appliedLogAt γr sv.Metadata'.Index' x'.log ∗
          kvApplied γr.raft γr.kv A' x' ∗ srvRest E' γr A') ∗
        (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ □ mvcc.api.isMvcc kv E'.γ ∗ ⌜kv = E'.kv⌝) ∗ rnWalTokA γn (srvRAddr s) q ∗
        srvSnapOwn s ci E' γr γ' sv.Metadata'.Index' ∗
        ⌜loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' ∧
          A <+: A' ∧ (γr.raft.pre ++ A').length = uint.nat sv.Metadata'.Index' ∧
          lastTermIs A' sv.Metadata'.Term'⌝ }}

/-- **`s.applyAll(ep, ap)` on a snapshot payload, in the server's auth mode** (F9: one spec over
`E.authMode`, in place of the twin `specSnapOn`; lean's `applyAll.specSnap` is its `off` case,
`applyAll.specSnap_of_M`; the caller of `applySnapshot.specSnapM`): `applyAll.specSnap`'s statement
with the server's, the applier's and the KV's rows in the mode (`isServerM`/`srvApplyKVM`/
`kvAppliedM` at `E.authOn`, on at the applied log's auth state `sa`), the start's chain the mode's;
the store's snapshot clause, `srvAuthSnapOk`, is `srvSnapRO`'s gated row; after, at the image's auth
state. Read under `srvSnapRO`'s image certificate in the mode (review round 1's F5:
`srvSnapOwn`'s `srvSnapRO` holds `snapDirInv … (srvImage γr.raft.raft)`, the mode-off certificate,
false of an auth-on cluster's images; in the merge `srvImageM` at the cluster's mode, `srvImageOn` in the
mode `on`, from which `snapRecv_imageOn` gives `specSnapM`'s `hauthI`/`hkI`), and under
`authApplyResB`'s redefinition as `specSnapM` is. -/
abbrev EtcdServer.applyAll.specSnapM : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (ep ap : Loc) (es : GoSlice) (sn : Loc)
    (sv : SnapshotM) (rac nc : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (A : List EntryModel) (mst : Loc) (γs : MemStorNames) (γp : WTNames)
    (γnc : NotifyNames) (w : Nat) (nid : w64) (nk : GName) (q : Qp) (γn : RNNames) (rt : w64) (n : Nat)
    (sa : auth.AuthState),
  -- (F9) a mode the server runs in (the convention: `EtcdServer__apply.lean:44`)
  E.authMode ≠ .any →
  -- the snapshot past the applied index, below `2^61`, at least the boot log
  uint.Z ai < uint.Z sv.Metadata'.Index' → uint.Z sv.Metadata'.Index' < 2 ^ 61 →
  (γr.raft.raft.boot.length : Int) ≤ uint.Z sv.Metadata'.Index' →
  -- the applied log `A` through `ai`, the consistent index at most the applied one
  uint.Z ai = A.length → uint.Z (ciEff γ st.k) ≤ uint.Z ai →
  -- a fresh cluster's start (`snapRecv_image`'s), in either compaction mode (review R1's F7: a
  -- mode-on committed log has no compaction, `plainLogOn`, so its records are at `-1` in both)
  γr.raft = ⟨γr.raft.raft, [], W64 0⟩ → γr.kv.c0 = W64 0 →
  γr.kv.ch0 = apply.alarmChain E.authOn false false → γr.kv.log0 = [[], []] →
  -- (until the lease-expiry plan's S2–S4, 2026-11-05, also `γr.kv.lg = false`: a cluster that
  -- grants no lease, the lease-grant plan's D2 interim restriction)
  -- the batch's term good for a log at least the snapshot's (the merge's guard)
  γn.node = γr.raft.raft → uint.nat sv.Metadata'.Index' ≤ n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ isServerApplyAll s γr ∗ srvMemberIDAddr s ↦□ nid ∗
      -- the payload (`rnApSnap`'s)
      taEntriesAddr ap ↦□ es ∗ es ↦*□ ([] : List Loc) ∗
      taSnapshotAddr ap ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
      (letI := srvStor (GF := GF) γr.raft.raft; iprop(snapshotCert γr.raft.raft.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
        nodeSnapLocal γr.raft.raft.cl nid sv.Metadata'.Index')) ∗
      taNotifycAddr ap ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
      taRaftAdvancedCAddr ap ↦□ rac ∗
      rnAdvChan rac (letI := srvStor (GF := GF) ρ.raft.raft
        iprop(nodeAppliedLb ρ.raft.raft.cl nk (uint.nat sv.Metadata'.Index') ∗
          nodeCommitLb ρ.raft.raft.cl nk (uint.nat sv.Metadata'.Index') ∗
          srvFrozenAt γs (uint.nat sv.Metadata'.Index') ∗
          srvFrozenBelow γs (uint.nat sv.Metadata'.Index') ∗
          rnWalHanded γn (uint.nat sv.Metadata'.Index'))) ∗
      taRaftTermAddr ap ↦□ rt ∗ rnRtOk γn rt n ∗
      -- the apply thread's resources, as `spec`'s
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      srvSnapState s ep mst γs ai (W64 0) ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvBemuReaderAt s E.γbe ∗
      srvApplyKVM E.authOn s E ρ.wait x sa ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      srvWTPool E γp ∗ srvWTTaken γp.cnt w ∗ kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      srvApRes s γr A ∗ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ □ mvcc.api.isMvcc kv E.γ ∗ ⌜kv = E.kv⌝) ∗
      rnWalTokA γn (srvRAddr s) q ∗
      -- the snapshot path's resources (`srvSnapRO`'s configuration rebuild over
      -- `isServerApplyAll`'s two fields)
      -- (auth on: the store's invariant and snapshot clause are `srvSnapRO`'s row
      -- `authSnapKitM`)
      srvSnapOwn s ci E γr γ ai ∗
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
        ⌜beSucc γ E γ' E'⌝ ∗ isServerM E.authOn s γ' ci TM' E' ρ γr ∗ srvApRes s γr A' ∗
        srvRLogLb γr.raft A' ∗
        epAppliedIAddr ep ↦ sv.Metadata'.Index' ∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' ∗
        epConfState ep cs' ∗ epCsAt ρ.raft A' cs' ∗
        srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) ∗ applyThread γ' st' ∗
        applyBackend γ' ci b' ∗ ciApplying ci a t ∗
        srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E'.γ 1 ∗ srvBemuReaderAt s E.γbe ∗
        srvAppliedOwn γr sv.Metadata'.Index' ∗ appliedAtLeast γr sv.Metadata'.Index' ∗
        srvWTTaken γp.cnt w ∗
        (∃ x' : apply.ApplyKV, srvApplyKVM E.authOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') ∗
          appliedLogAt γr sv.Metadata'.Index' x'.log ∗
          kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A' x' (srvAuthAtLog γr.kv srvAuthSt0 A') ∗ srvRest E' γr A') ∗
        (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ □ mvcc.api.isMvcc kv E'.γ ∗ ⌜kv = E'.kv⌝) ∗ rnWalTokA γn (srvRAddr s) q ∗
        srvSnapOwn s ci E' γr γ' sv.Metadata'.Index' ∗
        ⌜loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' ∧
          A <+: A' ∧ (γr.raft.pre ++ A').length = uint.nat sv.Metadata'.Index' ∧
          lastTermIs A' sv.Metadata'.Term'⌝ }}

/-- **`applyAll`'s spec** (J8b, 2026-11-01): both cases, a batch of entries (`specBatch`) and a
snapshot payload, for the link; (the auth component's stage 2, 2026-11-04) both in the server's auth
mode (`specSnapM`; until then `specSnap`, the off case, now `specOff`'s, `ModeSpecs.lean`). -/
abbrev EtcdServer.applyAll.spec : Prop :=
  EtcdServer.applyAll.specBatch (GF := GF) (hG := hG) ∧
    EtcdServer.applyAll.specSnapM (GF := GF) (hG := hG)

end spec

end EtcdGrove
end Perennial
