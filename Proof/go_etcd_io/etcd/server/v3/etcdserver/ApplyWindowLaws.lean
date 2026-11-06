/-
**The apply chain's window forms at no window** (R2d, Q13 (a), 2026-11-06; DRAFT, the window-form
round: `notes/restart-plan.md`, "R2d Scope", its amendment). Lean-first (no Rocq counterpart).

`apply.spec`, `applyEntries.specBatch` and `applyAll.specBatch` are stated over a restarted
member's replay window (`ApplyWindow.lean`). Their texts before the window are kept here
(`…NoWin`, verbatim) with the laws that each is the window form's instance at no window
(`W = D = []`, `winOk_nil`): every window definition reduces to the no-window one by definition, so
each law is an instantiation (glue). A first start's callers (`run`'s proof, `ModeSpecs`) take the
window form and use its no-window instance unchanged.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntries
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SDRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `apply.spec` before the window (its text at lean `6b49f77e01`, unchanged through `aa4449beb6`). -/
abbrev EtcdServer.apply.specNoWin : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64) (ep : Loc) (cs : Loc)
    (rac : GoChan) (st : ApplyState) (a at0 : w64) (x : apply.ApplyKV) (γr : ReadNames)
    (A : List EntryModel) (γp : WTNames) (dv : Option Loc) (w : Nat) (sa : auth.AuthState),
  E.authMode ≠ .any → (E.authOn = true → receiptBound GF ≤ 2 ^ 48) →
  ms ≠ [] → entriesFrom f0 ms → loopOk γ st (f0 - 1) → logShapeM E.authOn E.lm ms →
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) f0 ms →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ srvLessorNilM E.authOn s ∗ batchWaitOk ρ E ms ∗ es ↦*□ ents ∗
      entriesAt ents ms ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a at0 ∗ epConfState ep cs ∗ epCsAt ρ.raft A cs ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKVM E.authOn s E ρ.wait x sa ∗ srvAppliedOwn γr (f0 - 1) ∗
      appliedLogAt γr (f0 - 1) x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗
      srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      kvBatch γr (ciEff γ st.k) (f0 - 1) A ms ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ ms) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗ srvApRes s γr A ∗
      -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
      srvTokRights E (ciEff γ st.k) }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"apply"))
      (Val #es)) (Val #ep)) (Val #rac))
  {{ (appliedt appliedi : w64) (shouldStop : Bool),
      RET (PairV (PairV #appliedt #appliedi) #shouldStop); srvFS s ∗ dvView ρ.raft dv (A ++ ms) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      srvApRes s γr (A ++ ms) ∗
      ∃ (st' : ApplyState) (a' at' : w64) (csl : Loc),
        applyThread γ st' ∗ srvTokRights E (ciEff γ st'.k) ∗ applyBackend γ ci b ∗
        ciApplying ci a' at' ∗
        epConfState ep csl ∗ epCsAt ρ.raft (A ++ ms) csl ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr appliedi ∗
        srvWTTaken γp.cnt (w + ms.length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVM E.authOn s E ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) ms x x'⌝ ∗ appliedLogAt γr appliedi x'.log ∗
          kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (A ++ ms) x' sa' ∗ srvRest E γr (A ++ ms)) ∗
        ⌜(ms.getLast?).map EntryModel.index = some appliedi ∧
          (ms.getLast?).map EntryModel.term = some appliedt ∧
          loopOk γ st' appliedi ∧
          uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi) ∧
          shouldStop = false⌝ }}

/-- **`apply.spec` at no window**. -/
theorem EtcdServer.apply.spec_noWin (h : EtcdServer.apply.spec (GF := GF) (hG := hG)) :
    EtcdServer.apply.specNoWin (GF := GF) (hG := hG) :=
  fun s γ ci TM E ρ b es ents ms f0 ep cs rac st a at0 x γr A γp dv w sa h1 h2 h3 h4 h5 h6 h7 =>
    h s γ ci TM E ρ b es ents ms f0 ep cs rac st a at0 x γr A γp dv w sa [] [] h1 h2 h3 h4 h5 h6 h7
      (winOk_nil _ _) (fun _ hm => nomatch hm)

/-- `applyEntries.specBatch` before the window (its text at lean `6b49f77e01`, unchanged through `aa4449beb6`). -/
abbrev EtcdServer.applyEntries.specBatchNoWin : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (ep ap : Loc) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64)
    (rac : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (γr : ReadNames) (A : List EntryModel) (γp : WTNames) (dv : Option Loc) (w : Nat) (sa : auth.AuthState),
  E.authMode ≠ .any → (E.authOn = true → receiptBound GF ≤ 2 ^ 48) →
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShapeM E.authOn E.lm (unapplied ai ms) →
  -- (D43 M3, 2026-10-25) the driver's view, `apply`'s
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (ai + 1) (unapplied ai ms) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServerM E.authOn s γ ci TM E ρ γr ∗ srvLessorNilM E.authOn s ∗ batchWaitOk ρ E ms ∗ taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗ epCsAt ρ.raft A cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗
      srvApplyKVM E.authOn s E ρ.wait x sa ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗ srvApRes s γr A ∗
      -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
      srvTokRights E (ciEff γ st.k) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #(); srvFS s ∗ dvView ρ.raft dv (A ++ unapplied ai ms) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      srvApRes s γr (A ++ unapplied ai ms) ∗
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        epCsAt ρ.raft (A ++ unapplied ai ms) cs' ∗
        applyThread γ st' ∗ srvTokRights E (ciEff γ st'.k) ∗ applyBackend γ ci b ∗
        ciApplying ci a' t' ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr ai' ∗ srvWTTaken γp.cnt (w + (unapplied ai ms).length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVM E.authOn s E ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' ∗ srvRest E γr (A ++ unapplied ai ms)) ∗
        ⌜loopOk γ st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          -- (D22 J5) one index per entry applied
          uint.Z ai' = uint.Z ai + (unapplied ai ms).length ∧
          -- (2026-10-31, the snapshot track: S1) the consistent index unchanged only for an empty batch
          ((unapplied ai ms = [] ∧ ciEff γ st'.k = ciEff γ st.k) ∨
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          -- (D22 S-h, 2026-10-20; S-0's amendment) the applied term: the last applied entry's
          termAfter at0 (unapplied ai ms) at'⌝ }}

/-- **`applyEntries.specBatch` at no window**. -/
theorem EtcdServer.applyEntries.specBatch_noWin
    (h : EtcdServer.applyEntries.specBatch (GF := GF) (hG := hG)) :
    EtcdServer.applyEntries.specBatchNoWin (GF := GF) (hG := hG) :=
  fun s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr A γp dv w sa h1 h2 h3 h4 h5 h6 h7 =>
    h s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr A γp dv w sa [] [] h1 h2 h3 h4 h5
      h6 h7 (winOk_nil _ _) (fun _ hm => nomatch hm)

/-- `applyAll.specBatch` before the window (its text at lean `6b49f77e01`, unchanged through `aa4449beb6`). -/
abbrev EtcdServer.applyAll.specBatchNoWin : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (C : AuthC) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (ep ap : Loc) (es : GoSlice)
    (ents : List Loc) (ms : List EntryModel) (f0 : w64) (rac nc : GoChan) (st : ApplyState)
    (ai at0 a t : w64) (cs : Loc) (x : apply.ApplyKV) (sa : auth.AuthState) (A : List EntryModel)
    (mst : Loc) (γs : MemStorNames) (γp : WTNames) (dv : Option Loc) (γnc : NotifyNames)
    (w : Nat) (nk : GName) (q : Qp) (γn : RNNames) (rt : w64) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      -- the component the environment's, and the batch's premises (`specBatchOff`'s, the shapes in
      -- the mode, `logShapeM`)
      ⌜E.authMode = C.mode ∧ acReceiptOk (GF := GF) C ∧
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
      srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗ srvApplyKVC C s E ρ.wait x sa ∗ srvAppliedOwn γr ai ∗
      appliedLogAt γr ai x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp.cnt w ∗
      kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ srvApRes s γr A ∗
      -- (2026-10-30, the repair) with a view, the apply side's half of the running token
      (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      -- (2026-10-31, #11) what the snapshot takes: the disk snapshot's storage, the server's KV over
      -- the store, the storage's invariant at the storage key `nk`, the apply side's half of the WAL token
      srvSnapDisk s γr ∗ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗
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
        srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗ srvAppliedOwn γr ai' ∗ appliedAtLeast γr ai' ∗
        srvWTTaken γp.cnt (w + (unapplied ai ms).length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVC C s E' ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' ∗ srvRest E' γr (A ++ unapplied ai ms)) ∗
        (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E'.s E'.γ) ∗ rnWalTokA γn (srvRAddr s) q ∗
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

/-- **`applyAll.specBatch` at no window**. -/
theorem EtcdServer.applyAll.specBatch_noWin
    (h : EtcdServer.applyAll.specBatch (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.specBatchNoWin (GF := GF) (hG := hG) := by
  intro s γ ci TM C E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x sa A mst γs γp dv γnc w nk
    q γn rt n
  have h' := h s γ ci TM C E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x sa A mst γs γp dv
    γnc w nk q γn rt n [] [] (winOk_nil _ _)
  -- the term row at Go's index: the whole ghost log at no window (`uint.Z ai = A.length`)
  by_cases hlen : uint.Z ai = A.length
  · have htake : A.take (uint.nat ai) = A := List.take_of_length_le (by
      have := uint_nat_eq ai; omega)
    rw [htake] at h'
    exact h'
  · iintro %Φ ⟨-, %hP, -⟩ -
    exact absurd hP.2.2.2.2.2.2.2.1 hlen

/-- **The no-window texts' running-token match is `srvRunH`** (stated with the match itself, so that
it is about the matcher the texts above elaborate to: `SDRun`'s lemmas name their specs' matchers). -/
theorem srvRunH_noWin (γs : ServerRaftNames) (dv : Option Loc) :
    (match dv with | none => (iprop(True) : IProp GF) | some n => (letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half)) =
      srvRunH γs dv := by
  cases dv <;> rfl

end laws

end EtcdGrove
end Perennial
