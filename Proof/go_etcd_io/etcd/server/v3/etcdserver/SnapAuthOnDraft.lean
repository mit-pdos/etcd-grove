/-
**The snapshot install with auth on (Draft; `notes/snapshot-auth-on-plan.md`).** Imported by
nothing. Statements top-down, proofs `sorry` but the glue and the ghost lemmas.

1. **The history's catch-up** (Q1 (b), proved): `authHistTie_catchup`, `catchup_list`.
2. **Q3 (b), the image**: `authDataOf`, `authBucketsAt` (over `schema.authBucketsAre`, with the
   revision's `uint64` bound), `authBucketsAt_after` (proved), `imageAtOn`/`dbImageOn`/`srvImageOn`,
   `SnapImageFactsOn`, `snapRecv_imageOn` (sorry), `srvHist_wf` (pure model facts, sorry: to check).
3. **The restated premise and contracts** (the user's decisions of 2026-11-01; candidate (ii),
   "record first", candidate (i) dropped): the per-backend names `auth.AuthBkNames` (`authWTok`,
   `authCur`, `authRetired`, the tie `authBkCur` at `γa.bk`, `authWHeld`), the published index's
   shares (`authPubQ`, `authPubTok`), the lifecycle `authBkLife` (retire, release, publish);
   redefined in place: `auth.authReadTxOk`/`authBackendOk` (guarded), `auth.beP`,
   `auth.revFresh`, `AonDraft.authPublishM`; one spec each: `AonDraft.auth.authStore.
   setRevision.spec`, `auth.authStore.Recover.spec` (over `auth.authOwnPM M hs N`);
   `auth.authCatchUpFirst` (proved), `auth.stepOk_of_fuelB` (proved).
4. **The premise** (trusted; one premise for boot and every snapshot): `AonDraft.authSchemaSrv`
   (boot's, changed in place) with the snapshot clause `authSchemaSnap`; `backend.rbOwnIn` (the
   backend's own idle part of a bucket set, `InvBackend.lean`); `authWAtHook`; N4 (2026-11-03, `R` a
   ticket): `authRdN`, `authRdSlots` (the store's share of a backend's reader slots, which both
   clauses take), `AonDraft.authRdSupply` (the kit's post).
5. **The apply thread's auth resource, redefined**: `AonDraft.authApplyResPre`/`authApplyResB`
   (the fuel at a base `authFuelB`, the lifecycle, the hook clause, `authStepsAny`).
6. **`Recover` at the install**: `authRecoverOn.spec` and its glue `authRecoverOn_glue` (proved
   from the restated `Recover.spec`, `authSchemaSnap`, `authBkLife`, `srvHist_wf`).
7. **The install and its callers**: `srvAuthSnapOk`, `srvImageM`, `AonDraft.srvRestOwn`,
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

/-- **The cap raised to a committed image's history** (the catch-up's tie half): with the store's
history `hs` at the applied log `A` (its latest state `A`'s) and a committed `A'` extending `A`,
`hs` is a prefix of `srvHist A'` and the cap is at least `srvHist A'`: every state of
`(srvHist A').drop hs.length` may be appended (`capLb` of the whole list covers each prefix). -/
theorem authHistTie_catchup (E : apply.AEnv GF) (γr : ReadNames) (γa : auth.AuthNames)
    (A A' : List EntryModel) (hs : List auth.AuthState) (E' : CoPset) (hM : E.authMode = .on γa)
    (hpre : A <+: A')
    (hl : hs.getLast? = some (srvAuthAtLog γr.kv (auth.bump auth.bootState) A))
    (hE1 : ↑authTieN ⊆ E') (hE2 : ↑(nroot.@"authRev") ⊆ E') :
    authHistTie E γr (auth.bump auth.bootState) ∗ srvRLogLb γr.raft A' ∗
        auth.authOwn (.on γa) hs ={E'}=∗
      auth.authOwn (.on γa) hs ∗ ⌜hs <+: srvHist γr.kv A'⌝ ∗ auth.capLb γa (srvHist γr.kv A') := by
  have hne : hs ≠ [] := by intro he; rw [he] at hl; cases hl
  have hlast : hs.getLast? = (srvHist γr.kv A).getLast? := by rw [hl, srvHist_last]
  unfold authHistTie
  rw [hM]
  iintro ⟨⟨⟨%stl, %R, #Hinv⟩, #Htinv⟩, #Hlb, Ho⟩
  imod auth.authOwn_capped stl R γa hs E' hE2 $$ [Hinv Ho] with ⟨Ho, #Hhc⟩
  · iframe Hinv Ho
  iinv Htinv with Hi Hclose
  icases Hi with ⟨%A₀, >#HA₀, >Hcap⟩
  ihave Hcap : auth.capAuth γa (srvHist γr.kv A₀) $$ [Hcap]
  · simp only [srvHist]; iexact Hcap
  ihave %Hcmp := srvRLogLb_prefix γr.raft A₀ A' $$ [HA₀ Hlb]
  · iframe HA₀ Hlb
  ihave %Hhs0 := capAuth_lb_prefixW γa _ hs $$ Hcap Hhc
  rcases Hcmp with h0 | h0
  · -- the cap's log is behind the image's: raise it to `A'`
    imod auth.capAuth_update γa (srvHist γr.kv A') (srvHist_prefix γr.kv A₀ _ h0) $$ Hcap
      with Hcap
    ihave ⟨Hcap, #Hcl⟩ := auth.capAuth_lb γa _ $$ Hcap
    imod Hclose $$ [Hcap] with -
    · inext; iexists A'; iframe Hlb; unfold srvHist; iexact Hcap
    imodintro
    iframe Ho Hcl
    ipureintro
    exact (by exact Hhs0 : hs <+: srvHist γr.kv A₀).trans (srvHist_prefix γr.kv A₀ _ h0)
  · -- the cap's log is at or past the image's: the history is the applied log's
    ihave ⟨Hcap, #Hcl0⟩ := auth.capAuth_lb γa _ $$ Hcap
    imod Hclose $$ [Hcap] with -
    · inext; iexists A₀; iframe HA₀; simp only [srvHist]; iexact Hcap
    have hseq : hs = srvHist γr.kv A :=
      prefix_eq_of_last _ hs _ (srvHist_nodup γr.kv A₀) Hhs0
        ((srvHist_prefix γr.kv A A' hpre).trans (srvHist_prefix γr.kv _ A₀ h0)) hlast hne
    ihave #Hcl : auth.capLb γa (srvHist γr.kv A') $$ [Hcl0]
    · iapply (auth.capLb_le γa (srvHist γr.kv A') (srvHist_prefix γr.kv A' A₀ h0)) $$ Hcl0
    imodintro
    iframe Ho Hcl
    ipureintro
    rw [hseq]; exact srvHist_prefix γr.kv A A' hpre

/-- **The skipped states and the image's** (pure): with `hs` a prefix of `srvHist A'`, the catch-up
appends `N := (srvHist A').drop hs.length`, after which the history is `srvHist A'`, whose last
state is `A'`'s (`srvHist_last`). `N` is empty when no admin entry was skipped and the image's
state is the applied one (the cap's list has no state twice: nothing may be appended then). -/
theorem catchup_list (γk : KVNames) (A' : List EntryModel) (hs : List auth.AuthState)
    (h : hs <+: srvHist γk A') :
    hs ++ (srvHist γk A').drop hs.length = srvHist γk A' ∧
      (hs ++ (srvHist γk A').drop hs.length).getLast? =
        some (srvAuthAtLog γk (auth.bump auth.bootState) A') := by
  obtain ⟨t, ht⟩ := h
  have hd : (srvHist γk A').drop hs.length = t := by
    rw [← ht, List.drop_left]
  rw [hd, ht]
  exact ⟨rfl, srvHist_last γk A'⟩

/-! ## Q3 (b): the auth buckets of a backend's data, and the mode-on image (`srvImageOn`) -/

/-- **The auth buckets of the buckets `r`** (a backend's data, or the tracked view of it,
`backend.rbData P D`): what the decoding `schema.authBucketsAre` reads. -/
def authDataOf (r : GMap GoString backend.BktData) : schema.AuthData :=
  ⟨(r.lookup go!"auth").getD ∅, (r.lookup go!"authUsers").getD ∅,
    (r.lookup go!"authRoles").getD ∅⟩

/-- **The auth buckets of `r` hold the state `st`** (`schema.authBucketsAre` of `authDataOf r`),
its revision a `uint64` (the bucket stores `u64Be (W64 st.revision)`, which alone does not bound
`st.revision`: the read contract's `uint.nat x = st.revision` needs it; review round 1's F2).
(Q3 (b)'s boot form, "empty buckets at the boot state", is not needed: what `NewAuthStore` leaves
holds `bump bootState`, `authBucketsAt_after`, so every image decodes with this one form.) -/
def authBucketsAt (st : auth.AuthState) (r : GMap GoString backend.BktData) : Prop :=
  schema.authBucketsAre st (authDataOf r) ∧ st.revision < 2 ^ 64

/-- **What `NewAuthStore` leaves holds the start's state** `bump bootState` (its buckets created,
the revision `1` committed): so an image taken before any admin entry decodes to `srvAuthSt0`. -/
theorem authBucketsAt_after (r : GMap GoString backend.BktData) :
    authBucketsAt (auth.bump auth.bootState) (authBucketsAfter r) := by
  have hA : ((authBucketsAfter r).lookup go!"auth").getD ∅ = authBoot := by
    simp [authBucketsAfter, GMap.lookup_insert_eq_iff]
  have hU : ((authBucketsAfter r).lookup go!"authUsers").getD ∅ = ∅ := by
    simp [authBucketsAfter, GMap.lookup_insert_eq_iff]
  have hR : ((authBucketsAfter r).lookup go!"authRoles").getD ∅ = ∅ := by
    simp [authBucketsAfter, GMap.lookup_insert_eq_iff]
  unfold authBucketsAt
  refine ⟨?_, by simp [auth.bump, auth.bootState]⟩
  unfold authDataOf schema.authBucketsAre
  rw [hA, hU, hR]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n v h; simp at h
  · intro n v h; simp at h
  · intro v h
    simp [authBoot, schema.authRevisionKey, GMap.lookup_insert_eq_iff] at h
    subst h; exact u64Be_length _
  · simp [schema.enabledOf, authBoot, schema.authEnabledKey, schema.authRevisionKey,
      GMap.lookup_insert_eq_iff, auth.bump, auth.bootState]
  · simp [authBoot, schema.authRevisionKey, GMap.lookup_insert_eq_iff, auth.bump, auth.bootState]
  · intro n; simp [auth.bump, auth.bootState]
  · intro n v h; simp at h
  · intro n; simp [auth.bump, auth.bootState]
  · intro n v h; simp at h

/-- **`D` is the mode-`on` image at index `i` of the server's entries `A`, the raft log being `L`**
(`imageAt` with the model in the mode `on` from the start's auth state `st₀`): the `Key` bucket
`kvModelOn`'s, the meta keys, the rest buckets but the auth ones the rest model's, and the auth
buckets the auth state after `A` (`srvAuthAtLog`). (Rebased on #7-cmp's Freeze, as `imageAt`:) the
`Key` bucket and the compaction records by the KV names' mode at records `r` of the committed log's
compaction revision. -/
def imageAtOn (γk : KVNames) (st₀ : auth.AuthState) (bootLog : List EntryM) (i : w64)
    (L A : List EntryModel) (D : backend.Data) : Prop :=
  (∃ r : mvcc.CmpRecs, mvcc.keyImageM γk.cmp (kvModelOn γk st₀ A) r D ∧ r.crev = crevOf γk A) ∧
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes = encMeta i ∧
    (∃ t : w64, backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes = encMeta t) ∧
    (∀ n ∈ restBuckets, ¬ auth.authBkts n →
      D.lookup n = bkRestOf γk.c0 bootLog L n) ∧
    authBucketsAt (srvAuthAtLog γk st₀ A) D ∧ mvcc.IdxWf (kvModelOn γk st₀ A) []

/-- `dbImage` in the mode `on` (with `dbImage`'s KV log receipt, #7-cmp's). -/
def dbImageOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (i : w64)
    (D : backend.Data) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageAtOn γk st₀ γ.raft.boot i (γ.pre ++ A) A D⌝ ∗
    ⧖ (mvcc.logCh (kvModelOn γk st₀ A)))

/-- **The image certificate of a cluster with auth on** (Q3 (b): a Draft `srvImageOn` beside
`srvImage`, switched with #7-on, when the cluster's mode moves into `SrvRaft`): `srvImage`'s, the
start's chain the mode `on`'s and the model's start state `srvAuthSt0`. -/
def srvImageOn (γ : SrvRaft) (i : w64) (D : backend.Data) : IProp GF :=
  iprop(∃ γk : KVNames, ⌜γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain true false false ∧
    γk.log0 = [[], []]⌝ ∗ dbImageOn ⟨γ, [], W64 0⟩ γk srvAuthSt0 i D)

/-- **The receiver's facts of a mode-on image** (`SnapImageFacts`, its `hauthb` replaced by the
auth buckets' state, its KV log the mode-on model's; rebased on #7-cmp's: the image's compaction
records `r`). -/
structure SnapImageFactsOn [GooseExts] (γr : ReadNames) (d : mvcc.KBReal) (D : backend.Data)
    (cl : Loc) (i : w64) (A A' : List EntryModel) (x : apply.ApplyKV) (R : mvcc.Log)
    (r : mvcc.CmpRecs) (memI : GMap w64 apply.MemberM) : Prop where
  pre : A <+: A'
  len : uint.Z i = A'.length
  log : [[], []] ++ R = kvModelOn γr.kv srvAuthSt0 A'
  hpre : x.log <+: [[], []] ++ R
  hkI : mvcc.keyImageM d.cm ([[], []] ++ R) r D
  /-- the records at the image's committed log's compaction revision -/
  crev : r.crev = crevOf γr.kv A'
  hmetaI : ∃ t : w64, metaIs D (i, t)
  hRok : mvcc.restoreLogOk R
  /-- the image's KV model short enough (the KV jump's bound; review round 1's F7) -/
  hlen : (kvModelOn γr.kv srvAuthSt0 A').length < 2 ^ 63
  hlease : ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅
  halarm : ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅
  /-- the auth buckets hold the state after the image's log -/
  hauthI : authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A') (backend.rbData d.P D)
  hmemb : ((backend.rbData d.P D).lookup go!"members").isSome ∧
    ((backend.rbData d.P D).lookup go!"members_removed").isSome ∧
    ((backend.rbData d.P D).lookup go!"cluster").isSome
  /-- the image's membership buckets the model's (review round 2's F5, as `SnapImageFacts`') -/
  himg : membership.clusterImageOk cl (backend.rbData d.P D) memI
  /-- the rest model's buckets the image's but the auth ones, its members `memI` (`specSnapM`'s
  `hA'`) -/
  hA' : (∀ n, ¬ auth.authBkts n →
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk.lookup n =
      (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D))).lookup n) ∧
    (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI

/-- The buckets of `srvRestOwn`'s part but the auth ones: neither the cluster's nor the auth
store's. -/
def restNonAuth (n : GoString) : Prop :=
  ¬ membership.clusterBkts n ∧ ¬ auth.authBkts n

/-- **The rest buckets' owner, redefined over the mode** (rebased on the backend-auth-split stage:
lean's owner, the cluster's buckets idle and the others a part, with the auth buckets left out of the
part in `on`; decision 1, "the mode-on `srvRest` holds
the auth buckets at the log's auth state"): in `on`, the client's half of the **non-auth** tracked
buckets at the rest model (the auth buckets' write authority is the auth realization's, their
contents the history's last state, which `authHistTie`/`kvRunAtOn` make the log's auth state;
finding 5's gap, the rest model's auth buckets staying `authBoot`, no longer reaches `srvRest`); in
the other modes today's `srvRestOwn` (`rbOwn` of every tracked bucket). `srvRestOwnH`, `E.RO`'s
equation in `srvSnapRO`/`specSnap`, takes the mode with it. -/
def AonDraft.srvRestOwn (M : auth.AuthMode) (γB : backend.BNames) (c : Loc) (r : apply.RestM) :
    IProp GF :=
  match M with
  | .on _ => iprop(backend.rbOwnIn γB membership.clusterBkts r.bk ∗ backend.rbPart γB restNonAuth r.bk ∗
      membership.clusterMem c r.mem ∗ ⌜memIdOk r.mem ∧ restPresent r.bk⌝)
  | _ => Perennial.EtcdGrove.srvRestOwn γB c r

theorem AonDraft.srvRestOwn_off (γB : backend.BNames) (c : Loc) :
    AonDraft.srvRestOwn (GF := GF) .off γB c = Perennial.EtcdGrove.srvRestOwn γB c := rfl

/-- **`srvRestOwnH` over the mode** (review R1's F3: the statements name it, so that in `on` the
auth buckets, which the install hands to the auth realization, are not counted in `E.RO`). -/
def AonDraft.srvRestOwnH (M : auth.AuthMode) (γB : backend.BNames) (c : Loc) (H : IProp GF)
    (r : apply.RestM) : IProp GF :=
  iprop(AonDraft.srvRestOwn M γB c r ∗ H)

theorem AonDraft.srvRestOwnH_off (γB : backend.BNames) (c : Loc) (H : IProp GF) :
    AonDraft.srvRestOwnH (GF := GF) .off γB c H = Perennial.EtcdGrove.srvRestOwnH γB c H := rfl

/-- **`snapRecv_image` in the mode `on`** (the receiver's use of `srvImageOn`; statement only). -/
theorem snapRecv_imageOn (γ : SrvRaft) (γr : ReadNames) (E : apply.AEnv GF) (i ai : w64)
    (D : backend.Data) (d : mvcc.KBReal) (A : List EntryModel) (x : apply.ApplyKV) (cl : Loc)
    (H : IProp GF) (sa : auth.AuthState) (hkb : E.γ.kb = some d)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain true false false) (hlog0 : γr.kv.log0 = [[], []])
    (hai : uint.Z ai = uint.Z γr.raft.ai0 + A.length) (hi : uint.Z ai < uint.Z i)
    (hboot : (γ.boot.length : Int) ≤ uint.Z i)
    (hRO : E.RO = AonDraft.srvRestOwnH E.authMode d.γB cl H) :
    ⊢ srvKVInvsOn E γr srvAuthSt0 -∗ srvImageOn γ i D -∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa -∗ srvRest E γr A -∗
      membership.isRaftCluster cl ={⊤}=∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      ∃ (A' : List EntryModel) (R : mvcc.Log) (r : mvcc.CmpRecs), srvRLogLb γr.raft A' ∗
        ⌜SnapImageFactsOn γr d D cl i A A' x R r
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem⌝ ∗
        mvcc.restoreRcptM d ([[], []] ++ R) ∗ mvcc.crevPermAt E.γ r.finRev ∗
        mvcc.crevPermAt E.γ r.crev := by
  sorry

/-- **The states of the committed log's history are well formed** (pure; the catch-up needs them:
`authHist` keeps `permKeysOk` of every state, `Recover` the image state's `permsFit`, the fuel
its size and a revision bound), of a mode-on log (`plainLogOn`; review R1's F2: without it false,
the model's `userAddF` refusing only the empty name while `authSmall` bounds names by `maxKeySize`;
`adminKindOk` bounds them). Statement only: to check against the model's admin steps (the
grant step's `isValidPermissionRange`, `StepSmall` of the eleven steps). The revision is `1` plus
the number of state-changing admin entries, so at most the log's length plus one (review round 1's
F3: `< 2^61` is false of `2^61 - 1` distinct `UserAdd`s). -/
theorem srvHist_wf (γk : KVNames) (A' : List EntryModel) (hlen : A'.length < 2 ^ 61)
    (hp : plainLogOn A') :
    (∀ x ∈ srvHist γk A', auth.permKeysOk x) ∧
      auth.permsFit (srvAuthAtLog γk srvAuthSt0 A') ∧
      auth.authSmall (srvAuthAtLog γk srvAuthSt0 A') ∧
      (srvAuthAtLog γk srvAuthSt0 A').revision ≤ A'.length + 1 := by
  sorry

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

/-- **The catch-up, before `Recover`** (candidate (ii); ghost only, proved): with the whole
authority at `hs` and the cap's permission at `hs ++ N` (`authHistTie_catchup`), the states of `N`
are appended to the history (the revision invariant's quarter with it, its cap bound raised to
`hs ++ N`); the admin side keeps the pending authority, the lock's share is at the new last state
`stI` (for the new backend's lock), and `stI` is recorded. (It opens only `revInv`'s `revCur`, which
the restatement leaves unchanged, and frames `revFresh`.) -/
theorem auth.authCatchUpFirst (stl : Loc) (R : IProp GF) (γa : auth.AuthNames)
    (hs N : List auth.AuthState) (stI : auth.AuthState) (E' : CoPset)
    (hE : ↑(nroot.@"authRev") ⊆ E') (hk : ∀ x ∈ N, auth.permKeysOk x)
    (hl : (hs ++ N).getLast? = some stI) :
    auth.authInv (GF := GF) stl R (.on γa) ∗ auth.authOwnF (.on γa) hs ∗
        auth.capLb γa (hs ++ N) ={E'}=∗
      auth.authOwnP γa hs N ∗ auth.authLockI (.on γa) stI ∗
        auth.authStateAt γa ((hs ++ N).length - 1) stI := by
  have hi : (hs ++ N)[(hs ++ N).length - 1]? = some stI := by
    rw [List.getLast?_eq_getElem?] at hl; exact hl
  simp only [auth.authOwnF]
  iintro ⟨#Hinv, ⟨Hh, ⟨%stl', %Hl, Hc⟩⟩, #Hcap⟩
  iunfold auth.authInv at Hinv
  icases Hinv with ⟨-, #Hrev, -⟩
  iinv Hrev with Hi Hclose
  iunfold auth.revInv at Hi
  icases Hi with ⟨%r, >Hr, Hv, >Hcur, Hf⟩
  iunfold auth.revCur at Hcur
  icases Hcur with ⟨%stc, Hc2, %Hrc, %hh, Hq, -⟩
  ihave %Hhh := auth.authHist_rev_agree γa hs hh $$ Hh Hq
  subst Hhh
  imod (auth.authHist_appendL γa hs N hk) $$ [Hh Hq] with ⟨Hh, Hq⟩
  · iframe Hh Hq
  imod (auth.authHist_stateAt_keep γa (hs ++ N) ((hs ++ N).length - 1) stI hi) $$ Hh
    with ⟨Hh, #Hst⟩
  imod Hclose $$ [Hr Hv Hc2 Hq Hf] with -
  · inext; iunfold auth.revInv; iexists r; iframe Hr Hv Hf
    iunfold auth.revCur; iexists stc; iframe Hc2; isplitr
    · ipureintro; exact Hrc
    · iexists hs ++ N; iframe Hq Hcap
  icases (auth.authHist_split γa (hs ++ N)).1 $$ Hh with ⟨Hh, Hlk⟩
  imodintro
  iframe Hst
  isplitl [Hh Hc]
  · iunfold auth.authOwnP; iframe Hh; iexists stl'; iframe Hc; ipureintro; exact Hl
  · iunfold auth.authLockI; iexists hs ++ N; simp only [auth.authLockShare]; iframe Hlk
    ipureintro; exact hl

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

/-- **The fuel's step bound at a base** (finding 1's `stepOk_of_fuel` variant, review round 2's S4):
`fuelOk hs K` with `K + 2 < 2^63` (the fuel at a base: `K = k + b`, `k` below the receipts' bound,
`b ≤ 2^61`). -/
theorem auth.stepOk_of_fuelB (γa : auth.AuthNames) (hs : List auth.AuthState) (R : auth.StepRel)
    (K : Nat) (hR : auth.StepSmall R) (hf : auth.fuelOk hs K) (hk : K + 2 < 2 ^ 63) :
    auth.stepOk (.on γa) hs R := by
  intro st hst
  simp only [auth.histLast] at hst
  obtain ⟨h1, h2⟩ := hf st hst
  refine ⟨by omega, ?_⟩
  intro o st' hro ho
  subst ho
  obtain ⟨h3, h4⟩ := hR st st' h2 hro
  exact auth.permsFit_of_small st' h4 (by omega)

end bk

/-! ## The premise: boot's and every snapshot backend's (trusted; one premise)

- **The store's `R`** is fixed at the store's construction (`beP`, the readers' `authRd`), so the
  snapshot clause is produced by the boot premise, at the boot's `R`, and carried (TaDa).
- **`Recover`'s own read** needs one `R`: the apply thread's copy of `RD` (in `authApplyResPre`).
- **The open share** `authOpenQ` of every server backend: a quarter, out of the apply thread's half
  (which keeps the other quarter); the old backend's comes back at its release, for its `Close`. -/

section premise
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The auth realization's share of a backend's open token** (a quarter). -/
def authOpenQ : Qp := (1 : Qp).half.half

/-- The auth buckets: lean's `auth.authBkts` (the backend-auth-split stage). -/
abbrev authBkts : GoString → Prop := auth.authBkts

-- `backend.rbOwnIn` (decision 1's per-bucket idleness) is the backend's own (`InvBackend.lean`,
-- landed with the backend stage, `a43af91055`); the Draft's opaque stand-in and its split law are gone
-- (the real split is `rbOwn_split`'s into two `rbPart`s, of which only a written-back one is idle).

/-- The schema auth backend `abl` over the backend `be`, with the logger `lg` (read-only). -/
def ablOn (abl : Loc) (be lg : Loc) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #be : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg)

instance ablOn_persistent (abl be lg : Loc) : Persistent (ablOn (GF := GF) abl be lg) := by
  unfold ablOn; infer_instance

/-- **The write contract at every schema auth backend on `d`'s backend, at its frozen hook**
(`authSchemaSrv`'s E3l/E3n clause), at the backend `γc`'s write token. -/
def authWAtHook (γa : auth.AuthNames) (d : mvcc.KBReal) (γc : auth.AuthBkNames) : IProp GF :=
  iprop(□ ∀ (abl' lg' : Loc) (W' Pk' : IProp GF) (f' : GoFunc),
    ablOn abl' d.be lg' -∗ backend.isBackend d.γB d.P W' Pk' d.be -∗ backend.plHookRO d.γB f' -∗
    ⌜f' ≠ func.nil⌝ -∗ auth.authWBackendOkR (authBkIface abl') (.on γa) Pk' #f' (auth.authWTok γc))

instance authWAtHook_persistent (γa : auth.AuthNames) (d : mvcc.KBReal) (γc : auth.AuthBkNames) :
    Persistent (authWAtHook (GF := GF) γa d γc) := by
  unfold authWAtHook; infer_instance

/-- **The auth store's reader slots of the backend `d`** (N4): its auth share (`backend.rdAuth`,
`backend.authRdN` slots, a part of the constructor's partition, P1), which
the boot premise and the snapshot clause hand the realization for good (review R4's F1: a permission
check's read transaction may outlive `beMu`, `store.go:941-947`, so the release cannot give them
back; `backend.Close` takes only the open token, which the slots carry no share of). A ticket `R` is
redeemed against a slot of the backend current at `lockedReadTx` (with a share of its currency
`Cu`, which the release takes whole), so the same `R` works on every backend. -/
def authRdSlots (d : mvcc.KBReal) : IProp GF :=
  backend.rdAuth d.γB d.P d.be

/-- **The auth store's reader supply** (N4; review R4's F2 and N2): what `authStoreKit`'s post gives
the server in place of today's `actualMaxReaders` copies of `RD`, in every mode: `authRdN - 1` plain
copies of the ticket, which the readers keep as long as they like (a gRPC slot, the apply thread's
`kvOwn`, the compactor), as today; the `authRdN`-th is the auth applier's, in `authApplyResPre`
(`Recover` reads with it). `NewServer` takes 66 of them. -/
def AonDraft.authRdSupply (RD : IProp GF) : IProp GF :=
  iprop([∗list] _x ∈ List.replicate (backend.authRdN - 1) (), RD)

/-- **The snapshot clause** (trusted; persistent, at the store's `R`): a backend `d` the apply
thread opened, its hook frozen, its tracked auth buckets `r` holding `st` (`authBucketsAt`), the
lock's share of the history at `st` (deposited, as at boot: `st` is the history's last, so
recorded and at an index no smaller than the published one), its open share `authOpenQ`, the
succession right (the previous backend retired), the client's idle half of the auth buckets
(`rbOwnIn … authBkts`: `r` is what its readers see), the auth buckets in its table and the store's
share of its reader slots (`authRdSlots`): schema's
auth backend `abl` over it meets, for fresh names `γc`, the guarded read contract at `R`, the write
contract at its hook and at every schema auth backend on it (`authWAtHook`), with the write token,
the whole currency and the lifecycle (`authBkLife`, its realization keeping the open share until
the release, and the slots for good). The readers' copies of `R` (tickets, the boot premise's) work on it
unchanged. The client keeps the other tracked buckets. -/
def authSchemaSnap (γa : auth.AuthNames) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
      (r : GMap GoString backend.BktData) (st : auth.AuthState),
    ⌜lg ≠ null⌝ -∗ ⌜authBucketsAt st r⌝ -∗ ablOn abl d.be lg -∗
    -- (review R1's F5) the auth buckets in the backend's table, as `NewAuthStore.spec` takes them
    ⌜d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI⌝ -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
    backend.rbOwnIn d.γB authBkts r -∗ authRdSlots d -∗
    backend.bOpen d.γB authOpenQ -∗
    auth.authLockI (.on γa) st -∗ auth.authSucc γa -∗
    |={⊤}=> ∃ γc : auth.AuthBkNames,
      auth.authBackendOk (authBkIface abl) R (.on γa) γc ∗ auth.authCur γc 1 ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) Pk #f (auth.authWTok γc) ∗
      authWAtHook γa d γc ∗ auth.authWTok γc ∗
      auth.authBkLife γa γc (backend.bOpen d.γB authOpenQ))

instance authSchemaSnap_persistent (γa : auth.AuthNames) (R : IProp GF) :
    Persistent (authSchemaSnap (GF := GF) γa R) := by
  unfold authSchemaSnap; infer_instance

/-- **`authSchemaSrv`, restated** (the premise of `NewServer.specM true`; one trusted premise for
boot and every snapshot): for any auth names, given what `NewAuthStore`'s axiom takes of the
server's backend, its open share `authOpenQ`, the batch lock's share of the history at the boot
state and **half the published index's authority** (decision 2), schema's auth backend `abl` over
`d` meets, for fresh names `γc`: the guarded read contract at a reader resource `R`, with the whole
currency; the write contract (with the hook `P f`) and at every schema auth backend on `d` at its
frozen hook, `CreateAuthBuckets`, at the write token `T := authWTok γc`; the publication quarter
and the lifecycle (its realization keeping the open share and a quarter of the published index's
authority); `authRdN` copies of `R` (tickets, backed by the store's share of the backend's reader
slots, `authRdSlots`, taken; N4); the constructor's critical section, whose `Post`
gives back the open share and the hook; and the snapshot clause at `R`. It takes the client's idle
half of the (empty) auth buckets (decision 1: their write authority stays with the realization; the
client keeps the others') and the succession right (one live backend).

Today's five refutations, against this text: (1) the latest clause takes `T`; (2) the published
index's authority is shared with the realization, publication needs `T`; (3) no `rbOwn` of the auth
buckets comes back; (4) `Cu`/`T` stand for an open share the realization keeps until both are
surrendered; (5) `T` and `Cu` are functions of `γc`, which `beP` and the apply thread share. Review
rounds A1/A2: the auth buckets taken idle (no pending write: the readers see `r`); the succession
right taken (one live backend). -/
def AonDraft.authSchemaSrv : IProp GF :=
  iprop(□ ∀ (γa : auth.AuthNames) (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
      (r : GMap GoString backend.BktData),
    ⌜lg ≠ null⌝ -∗
    ⌜(r.lookup go!"auth").getD ∅ = ∅ ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
      (r.lookup go!"authRoles").getD ∅ = ∅⌝ -∗
    ablOn abl d.be lg -∗
    ⌜d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI⌝ -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.bOpen d.γB qo -∗
    backend.bOpen d.γB authOpenQ -∗ authRdSlots d -∗
    backend.plHook d.γB func.nil -∗ ownToks d.γB.wb 2 -∗ backend.rbOwnIn d.γB authBkts r -∗
    auth.authSucc γa -∗
    auth.authLockI (.on γa) auth.bootState -∗ auth.authPubQ γa (1 : Qp).half 0 -∗
    |={⊤}=> ∃ (R P : IProp GF) (f : val) (Pre Q Post : IProp GF) (γc : auth.AuthBkNames),
      auth.authBackendOk (authBkIface abl) R (.on γa) γc ∗ auth.authCur γc 1 ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) P f (auth.authWTok γc) ∗
      authWAtHook γa d γc ∗
      □ ({{ auth.authWTok γc }} (App (Val #(methods
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
          go!"CreateAuthBuckets" #abl)) (Val #())) {{ RET #(); auth.authWTok γc }}) ∗
      auth.authWTok γc ∗ auth.authPubTok γa ∗
      auth.authBkLife γa γc (backend.bOpen d.γB authOpenQ) ∗
      mvcc.csContract P f Pre Q Post ∗
      ([∗list] _x ∈ List.replicate backend.authRdN (), R) ∗
      (Post -∗ backend.bOpen d.γB qo ∗ backend.plHook d.γB func.nil) ∗
      authSchemaSnap γa R)

instance AonDraft.authSchemaSrv_persistent : Persistent (AonDraft.authSchemaSrv (GF := GF)) := by
  unfold AonDraft.authSchemaSrv; infer_instance

/-! ## The apply thread's auth resource, redefined (decision 7) -/

/-- The admin side's fuel at a base `b` (finding 1). -/
def authFuelB (hs : List auth.AuthState) (b : Nat) : IProp GF :=
  iprop(∃ k : Nat, ⧗ k ∗ ⌜auth.fuelOk hs (k + b) ∧ b ≤ 2 ^ 61⌝)

theorem authFuelB_of_fuel (hs : List auth.AuthState) :
    auth.authFuel (GF := GF) hs ⊢ authFuelB hs 0 := by
  iintro H
  iunfold auth.authFuel at H
  icases H with ⟨%k, Hk, %Hf⟩
  iunfold authFuelB
  iexists k
  iframe Hk
  ipureintro
  exact ⟨by simpa using Hf, by decide⟩

/-- **The store's admin steps at every hook and backend** (persistent; what boot's construction
gives from the admin steps' specs, `isAuthStepsX_of_authInvTB`, for all `bel Pk f T`), so that an
install can rebuild `authApplyResB`'s hook facts at the new backend. -/
def authStepsAny (stl : Loc) (γa : auth.AuthNames) (RD : IProp GF) : IProp GF :=
  iprop(□ ∀ (bel : Loc) (Pk : IProp GF) (f : val) (T : IProp GF),
    apply.isAuthStepsX (auth.authIface stl) Pk f (.on γa) (auth.tieRes stl (.on γa))
      (adminW stl bel (.on γa) Pk f T) RD)

instance authStepsAny_persistent (stl : Loc) (γa : auth.AuthNames) (RD : IProp GF) :
    Persistent (authStepsAny (GF := GF) stl γa RD) := by
  unfold authStepsAny; infer_instance

/-- **`authApplyResPre`, redefined** (decision 7: the hook-generic form, on the backend `d`): in
`on γa`, the authority with **its fuel at a base** (`authFuelB`), the tie, the write contract and
the apply thread's write token on the current backend `γc` (`authWHeld`: `T` and the share of the
name), the publication quarter, the backend's **lifecycle** (its retirement), the **hook clause**
(`authWAtHook`), the admin steps at any hook (`authStepsAny`), the provider's admin share and the
auth applier's copy of `RD` (N4: what `Recover` reads the new backend with; `NewServer.lean:831`'s
first copy).
(Boot's form adds the token rights' empty authority, `ghostMapAuth γa.fresh`, as today's.) -/
def AonDraft.authApplyResPre (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState)
    (d : mvcc.KBReal) (RD : IProp GF) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f0 : val) (γc : auth.AuthBkNames)
      (be : GoInterface) (b : Nat),
      auth.authOwn (.on γa) hs ∗ authFuelB hs b ∗ auth.tieRes stl (.on γa) hs ∗
      auth.authWBackendOk be (.on γa) P f0 (auth.authWTok γc) ∗ auth.authWHeld γa γc ∗
      auth.authPubTok γa ∗ auth.authBkLife γa γc (backend.bOpen d.γB authOpenQ) ∗
      authWAtHook γa d γc ∗ authStepsAny stl γa RD ∗ auth.tpAdmin stl (.on γa) ∗ RD ∗
      ⌜hs.getLast? = some st⌝)
  | _ => iprop(True)

/-- **`authApplyResB`, redefined** (decision 7): `authApplyResPre` at the server's hook `Pk f`, which
the backend `d` has frozen; today's hook facts (`authWBackendAt d.be … Pk f T`,
`isAuthStepsX … (adminW …)`) are its laws, from `authWAtHook` and `authStepsAny`. -/
def AonDraft.authApplyResB (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState)
    (d : mvcc.KBReal) (Pk : IProp GF) (f : val) (RD : IProp GF) : IProp GF :=
  match M with
  | .on γa => iprop(AonDraft.authApplyResPre (.on γa) stl st d RD ∗
      ∃ (W : IProp GF) (f' : GoFunc), ⌜f = #f' ∧ f' ≠ func.nil⌝ ∗
        backend.isBackend d.γB d.P W Pk d.be ∗ backend.plHookRO d.γB f')
  | _ => iprop(True)

/-! ## `Recover` at the install, with auth on (the server-level triple, and its glue) -/

/-- **`ast.Recover(NewAuthBackend(lg, newbe))` at the install, auth on** (the mode-on case of
`authRecoverOk`, gated by `E.authMode` in the merge): the apply thread's auth resource on the old
backend `dO` at the applied log `A`'s state `sa`, the store's tie to the log (`authHistTie`), the
image's committed log `A'` extending `A`, the new backend `dn` opened with its hook frozen, the
client's idle half of its auth buckets `r` holding `A'`'s state (`rbOwnIn … authBkts`; the install
keeps the other buckets' half), its open share for the realization, and the snapshot clause at the
store's `R` (`RD` the checks' reader over it; `Recover` reads with the apply thread's copy, N4):
after `Recover`, the store on the new backend (`authBeOn`), the apply thread's auth resource on it at
`A'`'s state, and **the old backend's open share** (after an update: its release, for the close
goroutine; decision 3c; its reader slots stay the realization's, R4's F1). -/
abbrev authRecoverOn.spec : Prop :=
  ∀ (ast abl lg : Loc) (dO dn : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
    (r : GMap GoString backend.BktData) (γa : auth.AuthNames) (R RD : IProp GF) (E : apply.AEnv GF)
    (γr : ReadNames) (A A' : List EntryModel) (sa : auth.AuthState),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      authBeOn ast dO.be ∗ AonDraft.authApplyResPre (.on γa) ast sa dO RD ∗
      auth.authInv ast R (.on γa) ∗ authSchemaSnap γa R ∗ ⌜RD = auth.authRd ast R (.on γa)⌝ ∗
      authHistTie E γr srvAuthSt0 ∗ srvRLogLb γr.raft A' ∗
      -- (review R1's F2) the image's committed log a mode-on log (`kvInvOn`'s), whose admin entries
      -- are bounded (`adminKindOk`)
      ⌜A <+: A' ∧ sa = srvAuthAtLog γr.kv srvAuthSt0 A ∧ A'.length < 2 ^ 61 ∧ plainLogOn A'⌝ ∗
      ⌜lg ≠ null⌝ ∗ ablOn abl dn.be lg ∗
      ⌜dn.P.has mvcc.authBI ∧ dn.P.has mvcc.authUsersBI ∧ dn.P.has mvcc.authRolesBI⌝ ∗
      backend.isBackend dn.γB dn.P W Pk dn.be ∗ backend.plHookRO dn.γB f ∗ ⌜f ≠ func.nil⌝ ∗
      backend.rbOwnIn dn.γB authBkts r ∗ authRdSlots dn ∗
      backend.bOpen dn.γB authOpenQ ∗ ⌜authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A') r⌝ }}
    (App (Val (ast @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
      go!"Recover")) (Val #(authBkIface abl)))
  {{ RET #(); |={⊤}=> (authBeOn ast dn.be ∗
      AonDraft.authApplyResPre (.on γa) ast (srvAuthAtLog γr.kv srvAuthSt0 A') dn RD ∗
      backend.bOpen dO.γB authOpenQ) }}

end premise

section glue
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The glue: `Recover` at the install from the restated `Recover.spec`** (its `on` case): the
tie's catch-up half and the list, the old token retired for the lock's share (`authBkLife`'s
retire, the publication quarter with it), the history caught up before the call
(`authCatchUpFirst`), the snapshot clause at the new backend (fresh `γc`), `Recover`, then the old
backend released (its whole currency from `Recover`, the retired token: its open share and the
publication quarter back); the fuel moved to the image's base. -/
theorem authRecoverOn_glue (hRec : auth.authStore.Recover.spec (GF := GF) (hG := hG)) :
    authRecoverOn.spec (GF := GF) (hG := hG) := by
  intro ast abl lg dO dn W Pk f r γa R RD E γr A A' sa hM
  simp only [AonDraft.authApplyResPre]
  iintro %Φ ⟨#Hpkg, Hbeon, Hres, #Hinv, #Hsnap, %HRD, #Htie, #HA', %Hp, %Hlg, #Habl, %Hhas,
    #HisB, #Hhk, %Hf, Hrb, Hslots, HbO, %Hbk⟩ HΦ
  obtain ⟨hpre, hsa, hlen, hplain⟩ := Hp
  obtain ⟨hk, hfit, hsmall, hrev⟩ := srvHist_wf γr.kv A' hlen hplain
  icases Hres with ⟨%hs, %P0, %f0, %γc₀, %be, %b, Hown, Hfu, Htr, -, HTh, Hpub,
    #Hlife, -, #Hsteps, Htp, Hrd, %Hlast⟩
  iunfold auth.authWHeld at HTh
  icases HTh with ⟨HT, Hbk0⟩
  -- the tie's half: the history a prefix of the image's, the cap at it
  imod authHistTie_catchup E γr γa A A' hs ⊤ hM hpre (by rw [Hlast, hsa]; rfl) (by simp) (by simp)
    $$ [Hown] with ⟨Hown, %Hpfx, #Hcap⟩
  · simp only [srvAuthSt0] at *; iframe Htie HA' Hown
  obtain ⟨hcat, hcl⟩ := catchup_list γr.kv A' hs Hpfx
  -- the old backend's token retired: the lock's share, joined with the admin side's
  iunfold auth.authBkLife at Hlife
  icases Hlife with ⟨#Hret0, #Hrel0, -⟩
  imod Hret0 $$ [HT Hpub] with ⟨⟨%st0, Hlk⟩, Hrtd, Hsucc⟩
  · iframe HT Hpub
  ihave ⟨HoF, -⟩ := auth.authOwn_lockI_join (.on γa) hs st0 $$ Hown Hlk
  ihave #Hcap' : auth.capLb γa (hs ++ (srvHist γr.kv A').drop hs.length) $$ [Hcap]
  · rw [hcat]; iexact Hcap
  -- the history caught up before the call
  imod auth.authCatchUpFirst ast R γa hs ((srvHist γr.kv A').drop hs.length)
      (srvAuthAtLog γr.kv srvAuthSt0 A') ⊤ (by simp)
      (fun x hx => hk x (List.mem_of_mem_drop hx)) hcl $$ [Hinv HoF Hcap']
    with ⟨HoP, Hlk, -⟩
  · iframe Hinv HoF Hcap'
  -- the snapshot clause at the new backend
  ihave #Hsn := Hsnap
  iunfold authSchemaSnap at Hsn
  imod Hsn $$ %lg %abl %dn %W %Pk %f %r %(srvAuthAtLog γr.kv srvAuthSt0 A') [] [] Habl [] HisB Hhk
      [] Hrb Hslots HbO Hlk Hsucc
    with ⟨%γc, #HokH, HCu, #HwR, #HwH, HT', #Hlife'⟩
  · ipureintro; exact Hlg
  · ipureintro; exact Hbk
  · ipureintro; exact Hhas
  · ipureintro; exact Hf
  -- the apply thread's reader of the store: its `R`, for `Recover`
  rw [HRD]
  iunfold auth.authRd at Hrd
  icases Hrd with ⟨Hrd1, Hrd2, Hrd3, HR⟩
  -- `Recover`
  iunfold authBeOn at Hbeon
  icases Hbeon with ⟨%abl0, %lg0, -, Hbe, -, -⟩
  iunfold auth.tieRes at Htr
  icases Htr with ⟨%b0, %sc, Hfl, #Hev, Hca, #Hsc, -⟩
  ihave Hen := auth.flagAt_enabledHalf ast (.on γa) b0 $$ [Hfl]
  · iframe Hfl Hev
  ihave Hch := auth.cacheHalf_of_at ast (.on γa) sc $$ Hca Hsc
  wp_apply (hRec ast R (.on γa) hs ((srvHist γr.kv A').drop hs.length)
      (srvAuthAtLog γr.kv srvAuthSt0 A') (authBkIface abl) γc₀ γc)
      $$ [Hbe Hen Hch Htp HR HoP HT' HCu Hbk0]
    as ⟨Htp, HR, Hbe, ⟨Hown, Htr⟩, Hout⟩
  · iframe Hinv Hen Hch Htp HR HokH
    isplitl [HoP]
    · simp only [auth.authOwnPM]; iexact HoP
    isplitl [Hbe]
    · iexists authBkIface abl0; iexact Hbe
    isplitr
    · ipureintro; simp [authBkIface]
    isplitl [HT' HCu Hbk0]
    · simp only [auth.recoverIn]; iframe HT' HCu Hbk0
    simp only [auth.recoverFit]
    ipureintro
    exact ⟨hcl, hfit⟩
  iunfold auth.recoverOut at Hout
  icases Hout with ⟨HT', Hbk', HCu0⟩
  iapply HΦ
  -- the old backend released: its open share and the publication quarter back
  imod Hrel0 $$ [Hrtd HCu0] with ⟨HoO, Hpub⟩
  · iframe Hrtd HCu0
  imodintro
  iframe HoO
  isplitl [Hbe]
  · iunfold authBeOn; iexists abl, lg
    iunfold ablOn at Habl
    icases Habl with ⟨#H1, #H2⟩
    iframe Hbe H1 H2; ipureintro; exact Hlg
  ihave #Hw := auth.authWBackendOk_of_R (authBkIface abl) (.on γa) Pk #f (auth.authWTok γc) $$ HwR
  iexists hs ++ (srvHist γr.kv A').drop hs.length, Pk, #f, γc, authBkIface abl,
    (srvAuthAtLog γr.kv srvAuthSt0 A').revision
  iframe Hown Htr Hw Hpub Hlife' HwH Hsteps Htp
  isplitl [Hfu]
  · iunfold authFuelB at Hfu
    icases Hfu with ⟨%k, Hk, -⟩
    iunfold authFuelB
    iexists k
    iframe Hk
    ipureintro
    refine ⟨?_, by omega⟩
    intro x hx
    rw [hcl] at hx
    cases hx
    exact ⟨by simp only [srvAuthSt0] at *; omega, hsmall⟩
  isplitl [HT' Hbk']
  · iunfold auth.authWHeld; iframe HT' Hbk'
  isplitl [Hrd1 Hrd2 Hrd3 HR]
  · iunfold auth.authRd; iframe Hrd1 Hrd2 Hrd3 HR
  ipureintro; exact hcl

end glue

/-! ## The install in the server's auth mode (`specSnapM`) and its caller -/

section install
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's auth store with its snapshot clause** (persistent; auth on; decision 8:
`NewServer`, `bootOk` and `isServerRunOn` carry it, as they do `#HmetaSnap`): the store its
`authStore` field holds, its invariant at its backend's read resource `R`, the snapshot clause at
`R`, and the apply environment's reader resource `RD` the checks' `authRd` over `R`. (Until this
round the draft took the invariant and the clause at `RD` itself: a bug of the draft, `authInv`'s
`R` being the backend's read resource and the server's `E.RD` the checks' `authRd ast R`, as
`authStoreKit_on` builds it.) -/
def srvAuthSnapOk (s : Loc) (γa : auth.AuthNames) (RD : IProp GF) : IProp GF :=
  iprop(∃ (ast : Loc) (R : IProp GF), srvAuthStoreAddr s ↦□ auth.authIface ast ∗
    auth.authInv ast R (.on γa) ∗ authSchemaSnap γa R ∗
    ⌜RD = auth.authRd ast R (.on γa)⌝)

instance srvAuthSnapOk_persistent (s : Loc) (γa : auth.AuthNames) (RD : IProp GF) :
    Persistent (srvAuthSnapOk (GF := GF) s γa RD) := by
  unfold srvAuthSnapOk; infer_instance

/-- **The image certificate in the cluster's auth mode** (decision 7; #7-on (b), the user's go-ahead
of 2026-11-03 after review R1's F8): `srvImageOn` when the cluster runs auth on, `srvImage`
otherwise (by `rfl`). Keyed on the **cluster's** mode, not a member's `E.authMode`: the certificate
travels in the cluster's network payload (`srvNet`), which every member's transport and snapshot
directory share. In the merge the mode is a field of `SrvRaft` (`authOn`, set by the allocator
`srvLogInv_alloc`, whose callers `NewServerAlloc`/`NewServerAllocOn` know it), and `NewServer` ties
it to the member's (`γr.raft.raft.authOn = E.authOn`): every member of a cluster boots in its mode. -/
def srvImageM (on : Bool) (γ : SrvRaft) (i : w64) (D : backend.Data) : IProp GF :=
  match on with
  | true => srvImageOn γ i D
  | false => srvImage γ i D

theorem srvImageM_off (γ : SrvRaft) : srvImageM (GF := GF) false γ = srvImage γ := rfl

instance srvImageM_persistent (on : Bool) (γ : SrvRaft) (i : w64) (D : backend.Data) :
    Persistent (srvImageM (GF := GF) on γ i D) := by
  cases on
  · simp only [srvImageM]; infer_instance
  · simp only [srvImageM]; unfold srvImageOn dbImageOn; infer_instance

/-- **The network payload in the cluster's auth mode** (#7-on (b)): `srvNet` with the image
certificate by the mode (`srvImageM`). In the merge `srvNet γ` is this at `γ.authOn`; the sender
(`applyAll`'s merge branch, `EtcdServer__applyAll.lean`'s #7-on) proves `srvImageOn` of an auth-on
member's database, the receiver (`snapRecv_imageOn`) reads it from the snapshot directory. -/
def AonDraft.srvNetM (on : Bool) (γ : SrvRaft) : NetPayload GF :=
  { srvNet γ with
    img := fun i D => srvImageM on γ i D
    img_pers := fun i D => by infer_instance }

/-- Mode off, today's payload. -/
theorem AonDraft.srvNetM_off (γ : SrvRaft) : AonDraft.srvNetM (GF := GF) false γ = srvNet γ := rfl

/-- **The apply thread's share of a server backend's open token, by the mode** (decision 5; review
R1's F1, R2's N1): a quarter in `on`, the auth realization keeping `authOpenQ`; the half otherwise.
In the merge `srvSnapRes` holds `bOpen d.γB (AonDraft.srvOpenQ E.authMode)` in place of its half
(and `NewServer`'s boot bundle with it), so that `srvSnapOwn` in `applyAll.specSnapM`/`applyResOn`
is at the quarter in `on`. -/
def AonDraft.srvOpenQ (M : auth.AuthMode) : Qp :=
  match M with
  | .on _ => (1 : Qp).half.half
  | _ => (1 : Qp).half

/-- **`srvSnapRO`'s two mode-dependent clauses, redefined** (decision 7 and 8): `srvSnapRO` is
today's with `snapDirInv ss γd (srvImage γr.raft.raft) …` replaced by `snapDirInv ss γd (srvImageM on
γr.raft.raft) …` at the cluster's mode `on` (`γr.raft.raft.authOn` in the merge), `E.RO = srvRestOwnH d.γB cl …` by its mode-indexed owner
(`AonDraft.srvRestOwn E.authMode`), and, beside `□ (⌜E.authMode = off⌝ → authRecoverOk ast)`, the
mode-`on` row `□ ∀ γa, ⌜E.authMode = .on γa⌝ → srvAuthSnapOk s γa E.RD` (the gated `Recover` facts
of decision 5), and (review R3's N2, R2's N3) among its facts beside `alarmBI` (`SnapRO.lean:394`)
the auth buckets in the table (`d.P.has authBI ∧ authUsersBI ∧ authRolesBI`, `NewServer`'s), which
`snapAuthImgM`'s `on` arm takes. Drafted as the delta, the rest of the bundle unchanged. -/
def AonDraft.srvSnapROAuth (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γd : GName)
    (ss : Loc) (γt : GName) : IProp GF :=
  iprop(inv snapDirN (snapDirInv ss γd (srvImageM on γr.raft.raft) (srvSnapRm γt γr)) ∗
    □ (∀ γa : auth.AuthNames, ⌜E.authMode = .on γa⌝ → srvAuthSnapOk s γa E.RD))

/-- **`srvSnapApplied` with auth on**: the server's row in the mode, the applier at the image's
auth state (the state after `A'`). -/
def srvSnapAppliedOn (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (R : mvcc.Log) (r : mvcc.CmpRecs)
    (A' : List EntryModel)
    (ss : Loc) (bp : GoString) (γt : GName) (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds)
    (idm : w64) (lp al ast cl : Loc) : IProp GF :=
  iprop(∃ (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (E' : apply.AEnv GF) (b' : GoInterface)
      (st' : ApplyState) (d' : mvcc.KBReal) (x' : apply.ApplyKV) (cs' : Loc) (L : List w64),
    ⌜beSucc γ E γ' E' ∧ E'.γ.kb = some d' ∧ d'.cm = d.cm ∧ d'.P = d.P ∧
      E'.RO = AonDraft.srvRestOwnH E'.authMode d'.γB cl (srvObjsOn al ast lp cl d'.be) ∧
      loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' ∧
      x'.log = [[], []] ++ R ∧ x'.crev = r.crev ∧ x'.chain = apply.alarmChain E.authOn false false ∧
      (∀ f, (netRh γn).member f → f ≠ idm → f ∈ L)⌝ ∗
    isServerM true s γ' ci TM' E' ρ γr ∗
    epAppliedIAddr ep ↦ sv.Metadata'.Index' ∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' ∗
    epDiskSnapAddr ep ↦ sv.Metadata'.Index' ∗ epMemSnapAddr ep ↦ sv.Metadata'.Index' ∗
    epConfState ep cs' ∗ csOptA cs' DFrac.discard sv.Metadata'.ConfState' ∗
    applyThread γ' st' ∗ applyBackend γ' ci b' ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
    srvApplyKVOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') ∗ srvRest E' γr A' ∗ srvKVCloserW s E' ∗
    -- (review R1's F1, decision 5) the apply thread's open share a quarter in `on`: the auth
    -- realization keeps `authOpenQ`
    backend.isStopChans d'.γB d'.be ∗ backend.bOpen d'.γB (AonDraft.srvOpenQ E'.authMode) ∗
    monoNatAuthOwn γt 1 (uint.nat sv.Metadata'.Index') ∗
    backend.pathOwn bp ∗
    trLive γn t c L ∗
    (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E'.s E'.γ))

/-- **`specSnapM`'s post, by the mode** (F9): lean's `srvSnapApplied` off, `srvSnapAppliedOn`
on. -/
def srvSnapAppliedM (on : Bool) (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (R : mvcc.Log)
    (r : mvcc.CmpRecs) (A' : List EntryModel) (ss : Loc) (bp : GoString) (γt : GName)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (idm : w64) (lp al ast cl : Loc) :
    IProp GF :=
  match on with
  | false => srvSnapApplied s ep sv γ ci E ρ γr d R r A' ss bp γt γn t c rs idm lp al ast cl
  | true => srvSnapAppliedOn s ep sv γ ci E ρ γr d R r A' ss bp γt γn t c rs idm lp al ast cl

/-- **The image's auth facts by the auth mode** (F9, the user's decision of 2026-11-03: one
`specSnap` over `E.authMode`): `off`, lean's `hauthb` (the auth buckets at `authBoot`/empty); `on`,
the auth buckets in the table, the image's auth buckets holding the state after its log `A'`, which
extends the applied log `A`, below raft's bound (`snapRecv_imageOn`'s); `any`, nothing (excluded by
the specs' `E.authMode ≠ .any`). -/
def snapAuthImgM (M : auth.AuthMode) (γr : ReadNames) (P : backend.BParams) (D : backend.Data)
    (A A' : List EntryModel) : Prop :=
  match M with
  | .off => ((backend.rbData P D).lookup go!"auth").getD ∅ = authBoot ∧
      ((backend.rbData P D).lookup go!"authUsers").getD ∅ = ∅ ∧
      ((backend.rbData P D).lookup go!"authRoles").getD ∅ = ∅
  | .on _ => (P.has mvcc.authBI ∧ P.has mvcc.authUsersBI ∧ P.has mvcc.authRolesBI) ∧
      authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A') (backend.rbData P D) ∧
      A <+: A' ∧ A'.length < 2 ^ 61
  | .any => True

/-- **The rest model's buckets after the snapshot's entries `A'`, by the mode** (F9; S8d's named
premise): the image's rest buckets (with the lessor's and the alarm store's emptied by their
`Recover`); with auth on, all but the auth ones (the rest model does not model the admin writes:
its auth buckets stay `authBoot`). -/
def snapRestImgM (on : Bool) (γr : ReadNames) (P : backend.BParams) (D : backend.Data)
    (A' : List EntryModel) : Prop :=
  match on with
  | false => (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk =
      <[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData P D))
  | true => ∀ n, ¬ auth.authBkts n →
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk.lookup n =
      (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData P D))).lookup n

/-- **The auth store's `Recover` facts, by the mode** (F9): `off`, lean's `authRecoverOk`; `on`,
the store's invariant at the server's read resource with the snapshot clause (`srvAuthSnapOk`) and
the image's committed log (`srvRLogLb … A'`); `any`, nothing (excluded by the specs). -/
def snapAuthResM (M : auth.AuthMode) (s ast : Loc) (RD : IProp GF) (γr : ReadNames)
    (A' : List EntryModel) : IProp GF :=
  match M with
  | .off => authRecoverOk ast
  | .on γa => iprop(srvAuthSnapOk s γa RD ∗ srvRLogLb γr.raft A')
  | .any => iprop(True)

/-- **`s.applySnapshot(ep, ap)` with a non-empty snapshot, in the server's auth mode** (F9, the
user's decision of 2026-11-03: one spec over `E.authMode`, in place of the twin `specSnapOn`; lean's
`specSnap` is its `off` case, `specSnap_of_M`): `specSnap`'s statement with the mode-dependent
parts indexed by `E.authMode`: the server's and the applier's rows (`isServerM E.authOn`,
`srvApplyKVM` at the applied log's auth state), the rest model's buckets (`snapRestImgM`: on, all
but the auth ones), the image's auth facts (`snapAuthImgM`: off, `hauthb`; on, the auth buckets at
the state after the image's log `A'`, `A <+: A'`), `Recover`'s facts (`snapAuthResM`: off,
`authRecoverOk`; on, the store's invariant at the server's `E.RD` with the snapshot clause
`authSchemaSnap` and the committed `A'`), the apply contract in the mode, the open share
(`srvOpenQ`). After: `srvSnapAppliedM` (on, the applier at the image's auth state).

Read under the merge's redefinitions (review round 1's F4): `srvApplyKVOn`'s auth part,
`authApplyResB (.on γa)`, is `AonDraft.authApplyResB`'s form (the fuel at a base, the token's
retirement, the hook clause), which `Recover`'s glue needs and gives back; today's form
(`authOwnFu`, no retirement) cannot be carried over a jump (the plan note's findings 1 and 2). -/
abbrev EtcdServer.applySnapshot.specSnapM : Prop :=
  ∀
    (s ep ap sn : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai at0 dsi : w64) (nc : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss hk : Loc)
    (hi : uint.Z ai < uint.Z sv.Metadata'.Index')
    (d : mvcc.KBReal) (D : backend.Data) (lgh : Loc)
    (hkb : E.γ.kb = some d)
    (hdbo : storage.dbOpensOk) (hsop : storage.snapOpensOk)
    (hP : d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧ ciKeys d.P ∧ storage.hooksParams d.P)
    (hcfgl : cfg.Logger' ≠ null) (hmmap : storage.openMmapOk cfg)
    (tI : w64) (hmeta : metaIs D (sv.Metadata'.Index', tI))
    (st : ApplyState) (b : GoInterface)
    (hle : uint.Z (ciEff γ st.k) ≤ uint.Z sv.Metadata'.Index')
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (hRO : E.RO = AonDraft.srvRestOwnH E.authMode d.γB cl (srvObjsOn al ast lp cl d.be))
    (hlease : ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅)
    (hwq : E.γ.watchQ = true)
    (R : mvcc.Log) (hpre : x.log <+: [[], []] ++ R) (hRok : mvcc.restoreLogOk R)
    -- (as `specSnap`'s since M2's item 15) the image by the store's mode at its compaction records
    -- `r`, on past the store's compaction revision
    (r : mvcc.CmpRecs) (hcc : d.cm = true → x.crev ≤ r.crev)
    (hkI : mvcc.keyImageM d.cm ([[], []] ++ R) r D) (hbr : mvcc.bridgeParams d.P)
    -- (the lease-revoke plan, 2026-10-31) the `Lease` bucket in the table, tracked, no hook keys
    -- (the boot backend's, `bootOk`; the new backend's parameters are the old one's)
    (hlp : mvcc.leaseParams d.P)
    (γp : GName) (hrbw : receiptBound GF ≤ backend.wbInit - 6)
    (stp : Loc) (γd γt : GName) (img : w64 → backend.Data → IProp GF) (nt : Nat)
    (hstp : storage.storageSnap stp ss) (hnt : nt ≤ uint.nat sv.Metadata'.Index')
    (halarm : ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅)
    -- (as `specSnap`'s, the backend-auth-split stage) the alarm bucket in the table
    (halbi : d.P.has mvcc.alarmBI)
    (hmemb : ((backend.rbData d.P D).lookup go!"members").isSome ∧
      ((backend.rbData d.P D).lookup go!"members_removed").isSome ∧
      ((backend.rbData d.P D).lookup go!"cluster").isSome)
    (memI : GMap w64 apply.MemberM)
    (himg : membership.clusterImageOk cl (backend.rbData d.P D) memI)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (dir : w64 → List GoString)
    (ps : List w64) (idm : w64)
    (hdir : γn.dir = dir) (hdok : netDirOk dir) (hps : ∀ f, dir f ≠ [] ↔ f ∈ ps)
    (hlid : c.lid = idm)
    (msi : w64) (cs0 : Loc) (fg : GoInterface) (quota : w64) (wad : time.Duration)
    (hbuq : apply.backendUnderQuota)
    -- (S8d's named premise, S-j1's) the snapshot's entries `A'`: the rest model after them is the
    -- image's rest buckets (with the lessor's and the alarm store's emptied by their `Recover`)
    -- and the decoded members
    (A' : List EntryModel)
    (hA' : snapRestImgM E.authOn γr d.P D A' ∧
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI)
    -- (F9) a mode the server runs in (the convention: `EtcdServer__apply.lean:44`), and the image's
    -- auth facts by it (`off`: lean's `hauthb`; `on`: `snapRecv_imageOn`'s), in place of `hoff`
    (hany : E.authMode ≠ .any) (hauthI : snapAuthImgM E.authMode γr d.P D A A')
    -- (2026-11-01, J8a-1, item 8) the payload's two-receive `notifyc` (`rnApSnap`'s), before its
    -- first receive (until then a unit bag)
    (γnc : NotifyNames),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       isServerM E.authOn s γ ci TM E ρ γr ∗
       taSnapshotAddr ap ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
       taNotifycAddr ap ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
       epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epDiskSnapAddr ep ↦ dsi ∗
       srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
       -- (as `specSnap`'s) the apply thread's token, given back
       threadTok ∗
       srvCfgAddr s ↦□ cfg ∗ structFieldRef EtcdServer go!"snapshotter" s ↦□ ss ∗
       structFieldRef EtcdServer go!"beHooks" s ↦□ hk ∗
       snap.isSnapshotter ss ∗ backend.fileHolds (snap.snapDBPath ss sv.Metadata'.Index') D ∗
       backend.pathOwn (config.backendPathOf cfg.DataDir') ∗
       (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
       storage.isBackendHooks hk
         ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #ci⟩ lgh ∗
       applyThread γ st ∗ applyBackend γ ci b ∗
       srvApplyKVM E.authOn s E ρ.wait x (srvAuthAtLog γr.kv srvAuthSt0 A) ∗ srvRest E γr A ∗
       lease.lessorInv lp E.γ.leases ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
       srvKVCloserW s E ∗
       (∃ (wsl : Loc) (γw0 : mvcc.WsNames), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
        mvcc.isWatchableStore wsl E.s γw0) ∗
       mvcc.certOk E.γ ([[], []] ++ R) ∗
       -- (as `specSnap`'s) on, the restored log's receipt and the compaction permits at the records
       mvcc.restoreRcptM d ([[], []] ++ R) ∗ mvcc.crevPermAt E.γ r.finRev ∗ mvcc.crevPermAt E.γ r.crev ∗
       □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b) ∗ srvWTPool E γp ∗
       rnStorageAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.storage.storage.ty) #stp : GoInterface) ∗
       -- (2026-11-01, J8a-1, item 8) the directory's removal fact `srvSnapRm`, as the server's
       -- bundle (`srvSnapRO`) has it (until then `snapTakenLb γt`, its first disjunct)
       inv snapDirN (snapDirInv ss γd img (srvSnapRm γt γr)) ∗ monoNatAuthOwn γt 1 nt ∗
       srvAlarmStoreAddr s ↦□ al ∗ isAlarmStore al ∗
       srvAuthStoreAddr s ↦□ auth.authIface ast ∗ srvClusterAddr s ↦□ cl ∗
       membership.isRaftCluster cl ∗
       rnTransportAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t : GoInterface) ∗
       trLive γn t c rs ∗ srvMemberIDAddr s ↦□ idm ∗
       srvMembersDir cl ps dir ∗
       epMemSnapAddr ep ↦ msi ∗ epConfState ep cs0 ∗
       srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗ isFeatureGate fg ∗
       srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ quota ∗
       srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ wad ∗
       -- (review R1's F1, decision 5) the apply thread's quarter
       backend.isStopChans d.γB d.be ∗ backend.bOpen d.γB (AonDraft.srvOpenQ E.authMode) ∗
       -- (F9) the auth store's `Recover` facts by the mode (`off`: `authRecoverOk`; `on`, Q2's
       -- candidate (ii): the store's invariant at the server's `E.RD` with the snapshot clause,
       -- and the image's committed log)
       snapAuthResM E.authMode s ast E.RD γr A' ∗
       -- (S8d's named premises, S-j1's: `NewServer`'s contracts of the stores on whichever backend)
       alarmApplyOk al ∗ authApplyOkM E.authMode ast E.RD ∗ lessorApplyOk lp ∗ clusterApplyOk cl ∗
       lease.lessorCfg lp ∗ lessorLookupOk lp ∗ (∃ n : Loc, membership.rcVersionChangedAddr cl ↦□ n) ∗
       -- (J8a-4, 2026-11-01, the user's decision: `notes/decisions.md`, "J8a-4") the meta reads of
       -- a backend the apply thread opens at the protocol's names `π` over an image whose meta keys
       -- are `π.m0`, from its fresh keys and payment rights (until then of any backend at any names
       -- with `π.m0` the snapshot's, false)
       □ (∀ (π : ApplyPhys) (γB : backend.BNames) (P : backend.BParams) (D : backend.Data),
         ⌜ciKeys P ∧ metaIs D π.m0 ∧ π.bwb = γB.wb ∧ π.bopn = γB.opn⌝ -∗
         backend.hkOwn γB (backend.hkData P D) -∗ backend.bFresh γB -∗
         backend.hkOwn γB (backend.hkData P D) ∗ backend.bFresh γB ∗
         □ ∀ (W : IProp GF) (b : Loc),
           backend.isBackend γB P W (batchLockInv (γ.withPh π) (metaTM γB P)) b -∗
           isMetaBackend (interface.mkOk (go.GoType.PointerType
             go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) (⊤ \ ↑applyN)
             (readView (γ.withPh π))) }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applySnapshot")) (Val #ep))
        (Val #ap))
    {{ RET #(); srvSnapAppliedM E.authOn s ep sv γ ci E ρ γr d R r A' ss (config.backendPathOf cfg.DataDir') γt γn t c rs idm lp al ast cl ∗
      notifyRcvN γnc 1 ∗ threadTok }}

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

/-- **Lean's `specSnap` is `specSnapM`'s `off` case** (F9): in the mode `off` every mode-indexed
part is lean's by `rfl`. -/
theorem EtcdServer.applySnapshot.specSnap_of_M
    (h : EtcdServer.applySnapshot.specSnapM (GF := GF) (hG := hG)) :
    EtcdServer.applySnapshot.specSnap (GF := GF) (hG := hG) := by
  intro s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl
    hmmap tI hmeta st b hle al ast lp cl x A hRO hlease hwq R hpre hRok r hcc hkI hbr hlp γp hrbw
    stp γd γt img nt hstp hnt halarm halbi hauthb hmemb memI himg γn t c rs dir ps idm hdir hdok
    hps hlid msi cs0 fg quota wad hbuq A' hA' hoff γnc
  have hon : E.authOn = false := by simp [apply.AEnv.authOn, hoff, auth.AuthMode.isOn]
  have H := h s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP
    hcfgl hmmap tI hmeta st b hle al ast lp cl x A (by rw [hoff]; exact hRO) hlease hwq R hpre
    hRok r hcc hkI hbr hlp γp hrbw stp γd γt img nt hstp hnt halarm halbi hmemb memI himg γn t c rs
    dir ps idm hdir hdok hps hlid msi cs0 fg quota wad hbuq A' (by rw [hon]; exact hA')
    (by rw [hoff]; simp) (by rw [hoff]; exact hauthb) γnc
  rw [hon, hoff] at H
  exact H

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
