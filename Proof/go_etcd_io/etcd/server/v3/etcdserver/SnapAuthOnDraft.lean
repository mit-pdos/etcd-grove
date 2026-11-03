/-
**The snapshot install with auth on (Draft; `notes/snapshot-auth-on-plan.md`).** Imported by
nothing. Statements top-down, proofs `sorry` but the glue and the ghost lemmas.

1. **The history's catch-up** (Q1 (b), proved): `authHistTie_catchup`, `catchup_list`.
2. **Q3 (b), the image**: `authDataOf`, `authBucketsAt` (over `schema.authBucketsAre`, with the
   revision's `uint64` bound), `authBucketsAt_after` (proved), `imageAtOn`/`dbImageOn`/`srvImageOn`,
   `SnapImageFactsOn`, `snapRecv_imageOn` (`SnapRecvOn.lean`, proved), `srvHist_wf` (pure model facts, sorry: to check).
3. **The restated premise and contracts** (the user's decisions of 2026-11-01; candidate (ii),
   "record first", candidate (i) dropped): the per-backend names `auth.AuthBkNames` (`authWTok`,
   `authCur`, `authRetired`, the tie `authBkCur` at `γa.bk`, `authWHeld`), the published index's
   shares (`authPubQ`, `authPubTok`), the lifecycle `authBkLife` (retire, release, publish);
   redefined in place: `auth.authReadTxOk`/`authBackendOk` (guarded), `auth.beP`,
   `auth.revFresh`, `AonDraft.authPublishM`; one spec each: `AonDraft.auth.authStore.
   setRevision.spec`, `auth.authStore.Recover.spec` (over `auth.authOwnPM M hs N`);
   `auth.authCatchUpFirst` (proved).
4. **The premise** (trusted; one premise for boot and every snapshot): `authSchemaSrv`
   (boot's, changed in place) with the snapshot clause `authSchemaSnap`; `backend.rbOwnIn` (the
   backend's own idle part of a bucket set, `InvBackend.lean`); `authWAtHook`; N4 (2026-11-03, `R` a
   ticket): `authRdN`, `authRdSlots` (the store's share of a backend's reader slots, which both
   clauses take), `authRdSupply` (the kit's post).
5. **The apply thread's auth resource, redefined**: `AonDraft.authApplyResPre`/`authApplyResB`
   (the fuel at a base `authFuelB`, the lifecycle, the hook clause, `authStepsAny`).
6. **`Recover` at the install**: `authRecoverOn.spec` and its glue `authRecoverOn_glue` (proved
   from the restated `Recover.spec`, `authSchemaSnap`, `authBkLife`, `srvHist_wf`).
7. **The install and its callers**: `srvAuthSnapOk`, `srvImageM`, `srvRestOwn`,
   `AonDraft.srvSnapROAuth`, `srvSnapAppliedOn`; F9 (2026-11-03): one spec over `E.authMode`,
   `applySnapshot.specSnapM` and `applyAll.specSnapM` (the mode-indexed `snapAuthImgM`,
   `snapRestImgM`, `snapAuthResM`, `srvSnapAppliedM`), lean's specs their `off` cases
   (`specSnap_of_M`, `applyAll.specSnap_of_M`, proved); `kvRunAtOn_sa` (proved), `run_snap_jobOn`
   (sorry).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthTie
public import Proof.go_etcd_io.etcd.server.v3.auth.CatchUpDraft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvImage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapAuthRecover
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Recover

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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


-- (P6.2, 2026-11-03) `authHistTie_catchup`, `catchup_list`, `srvHist_wf` are `SnapAuthRecover.lean`'s.


/-- The buckets of `srvRestOwn`'s part but the auth ones: neither the cluster's nor the auth
store's. -/
def restNonAuth (n : GoString) : Prop :=
  ¬ membership.clusterBkts n ∧ ¬ auth.authBkts n

/- (P5, 2026-11-03) The Draft's mode-indexed owner is now lean's `srvRestOwn`/`srvRestOwnH`,
mode-indexed in place (`InvRest.lean`, `restSet`). -/

-- (P6.1) `snapRecv_imageOn` is `SnapRecvOn.lean`'s (proved).
end draft

/-! ## The restated premise and contracts (the user's decisions of 2026-11-01)

Candidate (ii), "record first" (decision 4: candidate (i)'s statements dropped). The history is
caught up **before** `Recover`, ghost only (`authCatchUpFirst`): the skipped states and the image's
state `stI` are appended while the latest state's ghost variable (`authCurHalf`, tied to the
`revision` atomic by `revCur`) stays at the applied state; `Recover`'s `setRevision` then moves it.

The restatement (decisions 1-3, 5 and 7), all applying to **today's** `authSchemaSrv` too:
- **Per-backend ghost names** `γc : auth.AuthBkNames`: the write token `T := authWTok γc`, the
  currency `Cu q := authCur γc q`, the retired token `authRetired γc` are fixed functions of them
  (decision 3b); `beP` holds the current backend's `γc` in a ghost variable (`authBkCur`, at the
  new name `γa.bk`) whose other half travels with the apply thread's `T` (`authWHeld`).
- **The read contract guarded** (`auth.authReadTxOk`): the readers' clauses by `Cu q`
  (held by `beP`), the latest clause by `T`.
- **The open share** (decision 3a): each backend's realization keeps `bOpen γB authOpenQ`, given
  back (`authBkLife`'s release) only for both `authRetired γc` (from `T`) and `Cu 1`; `Recover`
  returns the old backend's `Cu₀ 1` (decision 3c).
- **The published index** (decision 2): the store's `revFresh` holds half its authority, the
  realization a quarter, the apply thread a quarter (`authPubTok`); publication needs `T` and the
  quarter (`authBkLife`'s publish clause), the token's retirement takes the quarter and the release
  gives it back, so nothing is published while a retired backend may still be read.
- **The auth buckets' write authority stays with the realization** (decision 1): the premise takes
  the client's half of the auth buckets (`rbOwnIn … authBkts`, a part of the backend's tracked-bucket
  token, idle: no pending write; review rounds A1's C, A2's 4); the client keeps the others'.
- **One live backend** (review rounds A1's A, A2's 1): both premises take the succession right
  `authSucc`.

Definitions redefining an existing one carry its name under `AonDraft.` (`auth.beP` for
`auth.beP`); the merge drops the prefix. Inside the bodies the originals are written in full
(`Perennial.EtcdGrove.auth.beP`) and the redefinitions with the prefix, to keep the two apart. -/

section bk
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]


-- (P6.2) `auth.authCatchUpFirst` is `SnapAuthRecover.lean`'s.

/-- **Publication, redefined** (`authPublishM`, decision 2): in `on γa`, for the current backend's
token (with its share of the current backend's name, `authWHeld`: publication is on `beP`'s
backend) and lifecycle, the publication quarter beside the authority and the tie (from the redefined
`revFresh`'s half and `authBkLife`'s publish clause; `authPublishM_of_authInv`, restated, not
drafted). -/
def AonDraft.authPublishM (M : auth.AuthMode) (stl : Loc) : IProp GF :=
  match M with
  | .on γa => iprop(□ ∀ (hs : List auth.AuthState) (γc : auth.AuthBkNames) (K : IProp GF),
      ⌜hs ≠ []⌝ -∗ auth.authBkLife γa γc K -∗ auth.authOwn (.on γa) hs -∗ auth.authWHeld γa γc -∗
      auth.authPubTok γa -∗ auth.tieRes stl (.on γa) hs ={⊤}=∗
      auth.authOwn (.on γa) hs ∗ auth.authWHeld γa γc ∗ auth.authPubTok γa ∗
        auth.tieRes stl (.on γa) hs ∗ auth.authPubLb γa (hs.length - 1))
  | _ => iprop(True)

-- (P6.2) `auth.stepOk_of_fuelB` is superseded: `auth.fuelOk` carries the base, `stepOk_of_fuel`.

end bk


/- (P6.2, 2026-11-03) `authRecoverOn.spec` and its glue `authRecoverOn_glue` are
`SnapAuthRecover.lean`'s. -/

/-! ## The install in the server's auth mode (`specSnapM`) and its caller -/

section install
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


/- (P6.2) `srvAuthSnapOk` is `SnapAuthRecover.lean`'s. -/


-- (P5, F8) `srvImageM` is `ImageOn.lean`'s.

/- (P5, F8) The Draft's `srvNetM` is lean's `srvNet`, whose image is `srvImageM γ.authOn`. -/

/- (P5) The Draft's `srvOpenQ` is now lean's (`InvRest.lean`). -/

/-- **`srvSnapRO`'s two mode-dependent clauses, redefined** (decision 7 and 8): `srvSnapRO` is
today's with `snapDirInv ss γd (srvImage γr.raft.raft) …` replaced by `snapDirInv ss γd (srvImageM on
γr.raft.raft) …` at the cluster's mode `on` (`γr.raft.raft.authOn` in the merge), `E.RO = srvRestOwnH d.γB cl …` by its mode-indexed owner
(`srvRestOwn E.authMode`), and, beside `□ (⌜E.authMode = off⌝ → authRecoverOk ast)`, the
mode-`on` row `□ ∀ γa, ⌜E.authMode = .on γa⌝ → srvAuthSnapOk s γa E.RD` (the gated `Recover` facts
of decision 5), and (review R3's N2, R2's N3) among its facts beside `alarmBI` (`SnapRO.lean:394`)
the auth buckets in the table (`d.P.has authBI ∧ authUsersBI ∧ authRolesBI`, `NewServer`'s), which
`snapAuthImgM`'s `on` arm takes. Drafted as the delta, the rest of the bundle unchanged. -/
def AonDraft.srvSnapROAuth (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γd : GName)
    (ss : Loc) (γt : GName) : IProp GF :=
  iprop(inv snapDirN (snapDirInv ss γd (srvImageM on γr.raft.raft) (srvSnapRm γt γr)) ∗
    □ (∀ γa : auth.AuthNames, ⌜E.authMode = .on γa⌝ → srvAuthSnapOk s γa E.RD))

/- (P6.2, 2026-11-03) `srvSnapAppliedOn` and `srvSnapAppliedM` are `SnapApplyDefs.lean`'s
(`srvSnapAppliedOn` as `srvSnapAppliedG true`, the same body). -/

/- (P6.2) `snapAuthImgM`, `snapRestImgM`, `snapAuthResM` are `SnapAuthRecover.lean`'s. -/

/- (P6.2, 2026-11-03) `applySnapshot.specSnapM` is the spec file's
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applySnapshot.lean`), `specSnap_of_M` its
proof file's. -/

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
    (x : apply.ApplyKV) (A : List EntryModel) (mst : Loc) (γs : MemStorNames) (γp : GName)
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
          srvFrozenBelow γs (uint.nat sv.Metadata'.Index'))) ∗
      taRaftTermAddr ap ↦□ rt ∗ rnRtOk γn rt n ∗
      -- the apply thread's resources, as `spec`'s
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      srvSnapState s ep mst γs ai (W64 0) ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗
      srvApplyKVM E.authOn s E ρ.wait x sa ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      srvWTPool E γp ∗ srvWTTaken γp w ∗ kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      srvApRes s γr A ∗ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗
      rnWalTok (srvRAddr s) q ∗
      -- the snapshot path's resources (`srvSnapRO`'s configuration rebuild over
      -- `isServerApplyAll`'s two fields)
      -- (auth on: the store's invariant and snapshot clause, `srvAuthSnapOk`, are `srvSnapRO`'s
      -- gated row, `AonDraft.srvSnapROAuth`)
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
        ⌜beSucc γ E γ' E'⌝ ∗ isServerM E.authOn s γ' ci TM' E' ρ γr ∗ srvApRes s γr A' ∗
        srvRLogLb γr.raft A' ∗
        epAppliedIAddr ep ↦ sv.Metadata'.Index' ∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' ∗
        epConfState ep cs' ∗ epCsAt ρ.raft A' cs' ∗
        srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) ∗ applyThread γ' st' ∗
        applyBackend γ' ci b' ∗ ciApplying ci a t ∗
        srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗
        srvAppliedOwn γr sv.Metadata'.Index' ∗ appliedAtLeast γr sv.Metadata'.Index' ∗
        srvWTTaken γp w ∗
        (∃ x' : apply.ApplyKV, srvApplyKVM E.authOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') ∗
          appliedLogAt γr sv.Metadata'.Index' x'.log ∗
          kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A' x' (srvAuthAtLog γr.kv srvAuthSt0 A') ∗ srvRest E' γr A') ∗
        (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E'.s E'.γ) ∗ rnWalTok (srvRAddr s) q ∗
        srvSnapOwn s ci E' γr sv.Metadata'.Index' ∗
        ⌜loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' ∧
          A <+: A' ∧ (γr.raft.pre ++ A').length = uint.nat sv.Metadata'.Index' ∧
          lastTermIs A' sv.Metadata'.Term'⌝ }}

/-- **The glue at `run`: the applied log's auth state** (what `specSnapM`'s applied auth state and
`applyAll.specSnapM`'s `kvAppliedM` take, on, from `applyResOn`'s `kvRunAtOn`): the KV row's model
pins the applier's auth state to the state after `A`. -/
theorem kvRunAtOn_sa (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel) (x : apply.ApplyKV)
    (sa : auth.AuthState) :
    kvRunAtOn (GF := GF) γr ai₀ c₀ A x sa ⊢
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗
        ⌜sa = srvAuthAtLog γr.kv srvAuthSt0 A ∧ γr.kv.c0 = c₀ ∧ γr.raft.ai0 = ai₀⌝ := by
  iintro H
  iunfold kvRunAtOn at H
  icases H with ⟨Hk, %Hc⟩
  iunfold kvAppliedOn at Hk
  icases Hk with ⟨Hl, %Hch⟩
  iunfold kvAppliedLOn at Hl
  icases Hl with ⟨H1, H2, H3, %He⟩
  isplitl
  · iunfold kvAppliedOn; iunfold kvAppliedLOn; iframe H1 H2 H3; ipureintro; exact ⟨He, Hch⟩
  ipureintro
  refine ⟨?_, Hc⟩
  unfold srvAuthAtLog
  rw [← He]

/-- **`run`'s auth-on snapshot-payload job** (review R1's F6: restated as the twin of J8b's
`run_job_snap`, `EtcdServer__run.lean`, statement only): its premises and resources, with the loop's
resources in the mode `on` (`applyResOn`; the store's snapshot clause is its `srvSnapOwn`'s
`srvSnapRO` row, review R2's N6); `applyAll.specSnapM` takes the loop from `A` to the image's log
`A'`. -/
theorem run_snap_jobOn (hAA : EtcdServer.applyAll.specSnapM (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (A A' : List EntryModel) (apL : Loc) (es : GoSlice) (sn : Loc)
    (sv : SnapshotM) (rac nc : GoChan) (γs : schedule.SchedNames) (γnc : NotifyNames)
    (γn : RNNames) (rt : w64) (γa : auth.AuthNames) (hM : C.E.authMode = .on γa)
    (ha00 : uint.nat C.ai₀ = 0) (hc0 : uint.Z C.c₀ ≤ uint.Z C.ai₀) (hpre : γn.pre = [])
    (hγn : γn.node = C.γr.raft.raft) (hρ : C.ρ.raft = C.γr.raft)
    (hpr : C.γr.raft.pre = γn.pre) (hγs : C.γs = γn.γs) (hγw : C.γw = C.ρ.wait)
    (hlt : A.length < A'.length)
    (hlen : (γn.pre ++ A').length = uint.nat sv.Metadata'.Index')
    (h61 : uint.Z sv.Metadata'.Index' < 2 ^ 61)
    (hboot : (γn.node.boot.length : Int) ≤ uint.Z sv.Metadata'.Index') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerApplyAll C.s C.γr ∗ srvMemberIDAddr C.s ↦□ γn.id ∗ srvMetaSnap C.γ ∗
        taEntriesAddr apL ↦□ es ∗ es ↦*□ ([] : List Loc) ∗
        taSnapshotAddr apL ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
        (letI := srvStor (GF := GF) γn.node; iprop(
          snapshotCert γn.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
          nodeSnapLocal γn.node.cl γn.id sv.Metadata'.Index')) ∗
        taNotifycAddr apL ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
        taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (letI := srvStor (GF := GF) γn.node
          iprop(nodeAppliedLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            nodeCommitLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            srvFrozenAt γn.γs (γn.pre ++ A').length ∗ srvFrozenBelow γn.γs (γn.pre ++ A').length)) ∗
        taRaftTermAddr apL ↦□ rt ∗ rnRtOk γn rt (rnLogOf γn A').length ∗
        schedule.schedRunning γs ∗ applyResOn C A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft A' }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyResOn C A' }} := by
  sorry

/-- **Lean's `applyAll.specSnap` is `applyAll.specSnapM`'s `off` case** (F9). -/
theorem EtcdServer.applyAll.specSnap_of_M
    (h : EtcdServer.applyAll.specSnapM (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.specSnap (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es sn sv rac nc st ai at0 a t cs x A mst γs γp γnc w nid nk q γn
    rt n hai hi61 hboot hAL hcia hraft hc0 hch hlog0 hγn hnI
  cases hon : E.authOn with
  | false =>
    have H := h s γ ci TM E ρ γr b ep ap es sn sv rac nc st ai at0 a t cs x A mst γs γp γnc w nid nk
      q γn rt n srvAuthSt0 (by rw [authMode_off_of E hon]; simp) hai hi61 hboot hAL hcia hraft hc0
      (by rw [hon]; exact hch) hlog0 hγn hnI
    rw [hon] at H
    exact H
  | true =>
    -- lean's rows are the mode `off`'s: its precondition refutes `authOn`
    wp_start as ⟨#Hsrv, #Hsa, #Hnid, #Hes, #Hesl, #Hsnf, Hsnv, ⟨#Hcert, #Hsloc⟩, #Hncf, #Hnc2, Hnr0,
      #Hracf, #Hracc, #Hrtf, #Hrt, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog,
      #HW, HWA, Hka, HRS, HAR, #Hkv, HwalT, Hso, #HmetaSnap⟩
    imod (authOn_false_of_off s γ ci TM E ρ γr ρ.wait x A) $$ [$Hsrv $HKV $Hka] with ⟨%Hoff, -, -⟩
    rw [hon] at Hoff
    cases Hoff

end install

end EtcdGrove
end Perennial
