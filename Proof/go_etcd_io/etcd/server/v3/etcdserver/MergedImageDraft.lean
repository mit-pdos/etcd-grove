/-
**Draft: `merged_image` restated, and `applyAll.specBatch`'s fresh-start premise**
(`notes/merged-image-plan.md`; `notes/decisions.md`, "`merged_image` is false with compaction on").
Imported by nothing; no `axiom`, no `sorry`. Nothing here is switched: the originals
(`SnapSendBranch.lean`'s `merged_image`, `EtcdServer.applyAll.specBatch`) are unchanged.

- `merged_image'`: `merged_image` with two premises, `E.cmp = false` (with compaction on the image
  can hold `Meta`'s `scheduledCompactRev` and lack compacted keys, and `srvImage` says neither) and
  the fresh start's raft names `γr.raft = ⟨γr.raft.raft, [], W64 0⟩` (`srvImage` is the fresh
  cluster's certificate; nothing in `isServer`/`kvApplied` fixes `pre`/`ai0`). Proved.
- `EtcdServer.applyAll.specBatchR`: `specBatch`'s text with the fresh start's raft names as a
  premise, beside the S1 premises (`specSnap` has the same one).
- `fresh_raft_of_newServer`: option B's glue (the fact in `isServerApplyAll`, from `NewServer`).
- `fresh_raft_of_run`: option A's glue at `specBatch`'s caller chain (`run` → `run_job_body` →
  `specBatch`): `run`'s facts (`isServerRun`'s `HEr`, `rnEnvOk`'s `Hnm`, `kvRun`'s `Hkc0`) give it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVChainOff
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll

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

/-- **Draft of `merged_image`** (the merged snapshot's image certificate, `srvNet`'s `img`), with
the compaction mode off (`hcmp`) and the fresh start's raft names (`hraft`). The image is
`srvImage` of the apply thread's KV names: `kvApplied` gives the committed `A` and
`x.log = kvModel γr.kv A`; `mergedObs`'s exact `Key` clause and `noCmpData` (both at `cmp = false`)
give `keyImage`; its `Meta` and rest clauses the rest of `imageAt`; the KV invariant the start
chain (`kvInv_ch0_off`). -/
theorem merged_image' (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (D : backend.Data) (hlen : uint.Z ai = A.length)
    (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []])
    (hcmp : E.cmp = false) (hraft : γr.raft = ⟨γr.raft.raft, [], W64 0⟩) :
    ⌜mergedObs γr E.cmp ai A x.log D⌝ ∗ isServer s γ ci TM E ρ γr ∗ kvApplied γr.raft γr.kv A x ⊢
      |={⊤}=> kvApplied γr.raft γr.kv A x ∗ □ (srvNet (GF := GF) γr.raft.raft).img ai D := by
  iintro ⟨%hobs, #Hsrv, Hka⟩
  rw [hcmp] at hobs
  obtain ⟨-, hkey, hnc, hci, hterm, hrest, hwf⟩ := hobs
  iunfold isServer at Hsrv
  icases Hsrv with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomics at Hat
  icases Hat with ⟨-, -, Hki⟩
  iunfold srvKVInvs at Hki
  icases Hki with ⟨#Hki, -⟩
  imod (kvInv_ch0_off γr.raft γr.kv) $$ Hki with %hch
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, %hx⟩
  iunfold kvAppliedL at Hka
  icases Hka with ⟨#HA, Hhi, Hcert, %hlog⟩
  imodintro
  isplitl [Hhi Hcert]
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HA Hhi Hcert
    ipureintro; exact ⟨hlog, hx⟩
  ihave #HA' : srvRLogLb (GF := GF) ⟨γr.raft.raft, [], W64 0⟩ A $$ []
  · rw [← hraft]; iexact HA
  iintro !>
  simp only [srvNet]
  iapply (srvImage_of_dbImage (γk := γr.kv) h0.1 hch h0.2)
  iunfold dbImage
  iexists A
  iframe HA'
  ipureintro
  have hpre : γr.raft.pre = [] := by rw [hraft]
  rw [hlog] at hkey hwf
  have hz : uint.Z (W64 0) = 0 := rfl
  refine ⟨by simp only []; omega, ⟨⟨hkey rfl, (hnc rfl).1, (hnc rfl).2⟩, hci, hterm, ?_, hwf⟩⟩
  simpa [hpre] using hrest

/-- **The glue at `specBatch`'s caller chain** (`run` → `run_job_body` → `specBatch`): the fresh
start's raft names from `run`'s facts: `kvRun`'s `γr.raft.ai0 = ai₀` (`Hkc0.2`), `rnEnvOk`'s
`Er.γr.raft.pre = γn.pre` (`Hnm.2.1`, with `HEγr : Er.γr = γr`), and `isServerRun`'s fresh start
`c₀ ≤ ai₀ ∧ γn.pre = [] ∧ ai₀ = 0` (`Hc0a`), all in scope where `run` calls `run_job_body`
(`EtcdServer__run.lean`, the job's body). -/
theorem fresh_raft_of_run (γr : ReadNames) (γn : RNNames) (ai₀ c₀ : w64)
    (hai : γr.raft.ai0 = ai₀) (hpre : γr.raft.pre = γn.pre)
    (hc0a : uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0) :
    γr.raft = ⟨γr.raft.raft, [], W64 0⟩ := by
  obtain ⟨-, hp, ha⟩ := hc0a
  cases h : γr.raft
  rw [h] at hai hpre
  simp only at hai hpre ⊢
  rw [hpre, hp, hai, ha]

/-- **Option B's glue** (`notes/merged-image-plan.md`): the fresh start's raft names as a conjunct
of `isServerApplyAll`'s start values (beside `c0`, `log0`, which are there for the merged image),
built by `NewServer` from its premise `ρ.rd.raft = ⟨γ, [], W64 0⟩` (`HρRaft`) and its `ρ.rd = γr`:
no premise of `specBatch` changes. -/
theorem fresh_raft_of_newServer (ρ : ReqNames) (γr : ReadNames) (γ : SrvRaft)
    (hrd : ρ.rd = γr) (hraft : ρ.rd.raft = ⟨γ, [], W64 0⟩) :
    γr.raft = ⟨γr.raft.raft, [], W64 0⟩ := by
  subst hrd; rw [hraft]

/-- **Draft of `applyAll.specBatch`** (`notes/merged-image-plan.md`): the text of `specBatch` with the
fresh start's raft names as a premise (`γr.raft = ⟨γr.raft.raft, [], W64 0⟩`, as `specSnap`'s), which
the merge branch passes to `merged_image'`. -/
abbrev EtcdServer.applyAll.specBatchR : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (ep ap : Loc) (es : GoSlice)
    (ents : List Loc) (ms : List EntryModel) (f0 : w64) (rac nc : GoChan) (st : ApplyState)
    (ai at0 a t : w64) (cs : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (mst : Loc) (γs : MemStorNames) (γp : GName) (dv : Option Loc) (γnc : NotifyNames)
    (w : Nat) (nk : GName) (q : Qp) (γn : RNNames) (rt : w64) (n : Nat),
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShape (unapplied ai ms) →
  -- (D43 M3, 2026-10-25) the driver's view, `apply`'s
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (ai + 1) (unapplied ai ms) →
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
  -- (draft, `notes/merged-image-plan.md`) the fresh start's raft names (`specSnap`'s), for the
  -- merged image (`merged_image'`)
  γr.raft = ⟨γr.raft.raft, [], W64 0⟩ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗ isServerApplyAll s γr ∗ batchWaitOk ρ E ms ∗
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
      -- the store, the storage's invariant at the storage key `nk`, the apply side's half of the WAL token
      srvSnapDisk s γr ∗ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗
      (letI : MemStorReg GF := ⟨γr.raft.raft.reg⟩; memStorInv mst γs γr.raft.raft.cl nk) ∗
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



/-- The restated spec is weaker: today's proof would give it. -/
theorem EtcdServer.applyAll.specBatchR_of_specBatch
    (h : EtcdServer.applyAll.specBatch (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.specBatchR (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x A mst γs γp dv γnc w nk q γn rt n
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 _
  exact h s γ ci TM E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x A mst γs γp dv γnc w nk q γn
    rt n h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end draft

end EtcdGrove
end Perennial
