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
   redefined in place: `AonDraft.auth.authReadTxOk`/`authBackendOk` (guarded), `AonDraft.auth.beP`,
   `AonDraft.auth.revFresh`, `AonDraft.authPublishM`; one spec each: `AonDraft.auth.authStore.
   setRevision.spec`, `AonDraft.auth.authStore.Recover.spec` (over `auth.authOwnPM M hs N`);
   `auth.authCatchUpFirst` (proved), `auth.stepOk_of_fuelB` (proved).
4. **The premise** (trusted; one premise for boot and every snapshot): `AonDraft.authSchemaSrv`
   (boot's, changed in place) with the snapshot clause `authSchemaSnap`; `backend.rbOwnIn` (the
   split of the tracked buckets' token, opaque, its law `rbOwn_split_in` a statement); `authWAtHook`.
5. **The apply thread's auth resource, redefined**: `AonDraft.authApplyResPre`/`authApplyResB`
   (the fuel at a base `authFuelB`, the lifecycle, the hook clause, `authStepsAny`).
6. **`Recover` at the install**: `authRecoverOn.spec` and its glue `authRecoverOn_glue` (proved
   from the restated `Recover.spec`, `authSchemaSnap`, `authBkLife`, `srvHist_wf`).
7. **The install and its callers**: `srvAuthSnapOk`, `srvImageM`, `AonDraft.srvRestOwn`,
   `AonDraft.srvSnapROAuth`, `srvSnapAppliedOn`, `applySnapshot.specSnapOn` (standalone, decision
   6), `applyAll.specSnapOn`, `kvRunAtOn_sa` (proved), `run_snap_jobOn` (sorry).
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
buckets the auth state after `A` (`srvAuthAtLog`). -/
def imageAtOn (γk : KVNames) (st₀ : auth.AuthState) (bootLog : List EntryM) (i : w64)
    (L A : List EntryModel) (D : backend.Data) : Prop :=
  mvcc.keyImage (kvModelOn γk st₀ A) D ∧
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes = encMeta i ∧
    (∃ t : w64, backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes = encMeta t) ∧
    (∀ n ∈ restBuckets, n ≠ go!"auth" → n ≠ go!"authUsers" → n ≠ go!"authRoles" →
      D.lookup n = bkRestOf γk.c0 bootLog L n) ∧
    authBucketsAt (srvAuthAtLog γk st₀ A) D ∧ mvcc.IdxWf (kvModelOn γk st₀ A) []

/-- `dbImage` in the mode `on`. -/
def dbImageOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (i : w64)
    (D : backend.Data) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageAtOn γk st₀ γ.raft.boot i (γ.pre ++ A) A D⌝)

/-- **The image certificate of a cluster with auth on** (Q3 (b): a Draft `srvImageOn` beside
`srvImage`, switched with #7-on, when the cluster's mode moves into `SrvRaft`): `srvImage`'s, the
start's chain the mode `on`'s and the model's start state `srvAuthSt0`. -/
def srvImageOn (γ : SrvRaft) (i : w64) (D : backend.Data) : IProp GF :=
  iprop(∃ γk : KVNames, ⌜γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain true false false ∧
    γk.log0 = [[], []]⌝ ∗ dbImageOn ⟨γ, [], W64 0⟩ γk srvAuthSt0 i D)

/-- **The receiver's facts of a mode-on image** (`SnapImageFacts`, its `hauthb` replaced by the
auth buckets' state, its KV log the mode-on model's). -/
structure SnapImageFactsOn [GooseExts] (γr : ReadNames) (d : mvcc.KBReal) (D : backend.Data)
    (cl : Loc) (i : w64) (A A' : List EntryModel) (x : apply.ApplyKV) (R : mvcc.Log)
    (memI : GMap w64 apply.MemberM) : Prop where
  pre : A <+: A'
  len : uint.Z i = A'.length
  log : [[], []] ++ R = kvModelOn γr.kv srvAuthSt0 A'
  hpre : x.log <+: [[], []] ++ R
  hkI : mvcc.keyImage ([[], []] ++ R) D
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
  /-- the rest model's buckets the image's but the auth ones, its members `memI` (`specSnapOn`'s
  `hA'`) -/
  hA' : (∀ n, n ≠ go!"auth" → n ≠ go!"authUsers" → n ≠ go!"authRoles" →
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk.lookup n =
      (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D))).lookup n) ∧
    (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI

/-- **`snapRecv_image` in the mode `on`** (the receiver's use of `srvImageOn`; statement only). -/
theorem snapRecv_imageOn (γ : SrvRaft) (γr : ReadNames) (E : apply.AEnv GF) (i ai : w64)
    (D : backend.Data) (d : mvcc.KBReal) (A : List EntryModel) (x : apply.ApplyKV) (cl : Loc)
    (H : IProp GF) (sa : auth.AuthState)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain true false false) (hlog0 : γr.kv.log0 = [[], []])
    (hai : uint.Z ai = uint.Z γr.raft.ai0 + A.length) (hi : uint.Z ai < uint.Z i)
    (hboot : (γ.boot.length : Int) ≤ uint.Z i)
    (hRO : E.RO = srvRestOwnH d.γB cl H) :
    ⊢ srvKVInvsOn E γr srvAuthSt0 -∗ srvImageOn γ i D -∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa -∗ srvRest E γr A -∗
      membership.isRaftCluster cl ={⊤}=∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      ∃ (A' : List EntryModel) (R : mvcc.Log), srvRLogLb γr.raft A' ∗
        ⌜SnapImageFactsOn γr d D cl i A A' x R
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem⌝ := by
  sorry

/-- **The states of the committed log's history are well formed** (pure; the catch-up needs them:
`authHist` keeps `permKeysOk` of every state, `Recover` the image state's `permsFit`, the fuel
its size and a revision bound). Statement only: to check against the model's admin steps (the
grant step's `isValidPermissionRange`, `StepSmall` of the eleven steps). The revision is `1` plus
the number of state-changing admin entries, so at most the log's length plus one (review round 1's
F3: `< 2^61` is false of `2^61 - 1` distinct `UserAdd`s). -/
theorem srvHist_wf (γk : KVNames) (A' : List EntryModel) (hlen : A'.length < 2 ^ 61) :
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
- **The read contract guarded** (`AonDraft.auth.authReadTxOk`): the readers' clauses by `Cu q`
  (held by `beP`), the latest clause by `T`.
- **The open share** (decision 3a): each backend's realization keeps `bOpen γB authOpenQ`, given
  back (`authBkLife`'s release) only for both `authRetired γc` (from `T`) and `Cu 1`; `Recover`
  returns the old backend's `Cu₀ 1` (decision 3c).
- **The published index** (decision 2): the store's `revFresh` holds half its authority, the
  realization a quarter, the apply thread a quarter (`authPubTok`); publication needs `T` and the
  quarter (`authBkLife`'s publish clause), the token's retirement takes the quarter and the release
  gives it back, so nothing is published while a retired backend may still be read.
- **The auth buckets' write authority stays with the realization** (decision 1): the premise takes
  the client's half of all tracked buckets (`rbOwn`) and gives back only the non-auth ones'
  (`rbOwnIn … restNonAuth`, a split of the backend's tracked-bucket token).

Definitions redefining an existing one carry its name under `AonDraft.` (`AonDraft.auth.beP` for
`auth.beP`); the merge drops the prefix. Inside the bodies the originals are written in full
(`Perennial.EtcdGrove.auth.beP`) and the redefinitions with the prefix, to keep the two apart. -/

section bk
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **The admin side's pending authority** (candidate (ii)): the history's half at `hs ++ N` (the
caught-up states recorded), the latest state's half still at `hs`'s last (the atomic not yet
stored). `N = []`: `authOwn (.on γa) hs`. -/
def auth.authOwnP (γa : auth.AuthNames) (hs N : List auth.AuthState) : IProp GF :=
  iprop(auth.authHistHalf γa (hs ++ N) ∗
    ∃ st : auth.AuthState, ⌜hs.getLast? = some st⌝ ∗ auth.authCurHalf γa st)

/-- **The pending authority in every mode** (decision 5: one `Recover.spec`): in `on γa`,
`authOwnP`; in the other modes, the authority at `hs ++ N` (no ghost variable to lag). -/
def auth.authOwnPM (M : auth.AuthMode) (hs N : List auth.AuthState) : IProp GF :=
  match M with
  | .on γa => auth.authOwnP γa hs N
  | _ => auth.authOwn M (hs ++ N)

/-- **The catch-up, before `Recover`** (candidate (ii); ghost only, proved): with the whole
authority at `hs` and the cap's permission at `hs ++ N` (`authHistTie_catchup`), the states of `N`
are appended to the history (the revision invariant's quarter with it, its cap bound raised to
`hs ++ N`); the admin side keeps the pending authority, the lock's share is at the new last state
`stI` (for the new backend's lock), and `stI` is recorded. (Over today's `authInv`: it opens only
`revInv`'s `revCur`, which the restatement leaves unchanged, and frames `revFresh`.) -/
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

/-! ### The per-backend ghost names (decision 3b) -/

/-- **A backend's auth ghost names** (the write token's, the currency's, the retired token's). -/
abbrev auth.AuthBkNames : Type := GName × GName × GName

/-- **The current backend's name** (a new field `bk` of `auth.AuthNames` in the merge, allocated
by `authBoot_alloc`; opaque here so that the draft leaves `AuthNames` as it is). -/
opaque auth.AuthNames.bk : auth.AuthNames → GName

/-- **The backend `γc`'s write token** `T` (exclusive): the apply thread's right to the backend's
auth batch, held outside a batch transaction (`Lock()` takes it, `Unlock()` gives it back). -/
def auth.authWTok (γc : auth.AuthBkNames) : IProp GF := token γc.1

/-- **The backend `γc`'s currency** `Cu q` (fractional): `beP` holds it with the backend, readers
under `beMu`'s read lock a part; `Recover` hands the old backend's whole `Cu 1` back. -/
def auth.authCur (γc : auth.AuthBkNames) (q : Qp) : IProp GF := ghostVar γc.2.1 q ()

/-- **The backend `γc` retired** (exclusive; what retiring `T` leaves). -/
def auth.authRetired (γc : auth.AuthBkNames) : IProp GF := token γc.2.2

/-- **The share `q` of the current backend's name**: `beP` holds half (at its fraction), the apply
thread the other half with the write token (`authWHeld`); the tie of `beP`'s `T` to the apply
thread's (review round 3's B). -/
def auth.authBkCur (γa : auth.AuthNames) (q : Qp) (γc : auth.AuthBkNames) : IProp GF :=
  ghostVar γa.bk q γc

theorem auth.authBkCur_agree (γa : auth.AuthNames) (q1 q2 : Qp) (γc γc' : auth.AuthBkNames) :
    ⊢ auth.authBkCur (GF := GF) γa q1 γc -∗ auth.authBkCur γa q2 γc' -∗ ⌜γc = γc'⌝ := by
  unfold auth.authBkCur
  exact ghostVar_agree γa.bk γc q1 γc' q2

/-- **The apply thread's write token on the current backend**: `T` and its half of the name. -/
def auth.authWHeld (γa : auth.AuthNames) (γc : auth.AuthBkNames) : IProp GF :=
  iprop(auth.authWTok γc ∗ auth.authBkCur γa (1 : Qp).half γc)

/-- **A share of the published index's authority** (`authPubAuth` is the whole). -/
def auth.authPubQ (γa : auth.AuthNames) (q : Qp) (p : Nat) : IProp GF := monoNatAuthOwn γa.pub q p

/-- **The apply thread's quarter of the published index's authority** (decision 2): with the
store's half (`revFresh`) and `T`, publication; retiring `T` gives it to the realization until the
release. -/
def auth.authPubTok (γa : auth.AuthNames) : IProp GF :=
  iprop(∃ p : Nat, auth.authPubQ γa (1 : Qp).half.half p)

/-- **A backend's lifecycle** (persistent; trusted, given by the premise with each backend's `γc`;
`K` what its realization keeps, `bOpen γB authOpenQ` for the server's backends):
- **retire**: `T` and the publication quarter for the lock's share of the history (the share is at
  rest in the realization while `T` is out of a batch; `Lock()` moves it out, `Unlock()` back) and
  the retired token: the backend's write contract and latest clause end with it;
- **release**: the retired token and the whole currency (no reader can begin a read) for `K` (the
  backend's open share, for its `Close`: decision 3a) and the publication quarter back;
- **publish**: with `T` (no batch open, the backend holds the history's last state), the
  publication quarter, the history's half at `hs` and the store's half at `p`, the published index
  raised to `hs`'s last. -/
def auth.authBkLife (γa : auth.AuthNames) (γc : auth.AuthBkNames) (K : IProp GF) : IProp GF :=
  iprop(□ (auth.authWTok γc ∗ auth.authPubTok γa ==∗
        (∃ st : auth.AuthState, auth.authLockI (.on γa) st) ∗ auth.authRetired γc) ∗
    □ (auth.authRetired γc ∗ auth.authCur γc 1 ==∗ K ∗ auth.authPubTok γa) ∗
    □ (∀ (hs : List auth.AuthState) (p : Nat), auth.authWTok γc -∗ auth.authPubTok γa -∗
        auth.authHistHalf γa hs -∗ auth.authPubQ γa (1 : Qp).half p -∗ ⌜p + 1 ≤ hs.length⌝ ==∗
      auth.authWTok γc ∗ auth.authPubTok γa ∗ auth.authHistHalf γa hs ∗
        auth.authPubQ γa (1 : Qp).half (hs.length - 1)))

instance auth.authBkLife_persistent (γa : auth.AuthNames) (γc : auth.AuthBkNames) (K : IProp GF) :
    Persistent (auth.authBkLife γa γc K) := by
  unfold auth.authBkLife; infer_instance

/-! ### The read contract, `beP` and `revFresh`, redefined in place -/

/-- **`authReadTxOk`, redefined** (review rounds 1-3's F1/F2/A; the axiom check's 13): in `on γa`,
for the backend `γc`:
- the readers' clause and the freshness clause take a part of the currency `Cu q` (given back at
  `RLock`): a retired, released backend's reads cannot begin (after its `Close` its read
  transaction dereferences a nil bolt transaction); a read begun before is safe, as Go's `Close`
  waits for the read transaction's holders (`batchTxBuffered.commit` takes `readTx.Lock()`);
- the latest clause takes the write token `T` with the history's half (`authHistHalf`, in `authOwn`
  and in the pending `authOwnP`): no batch of the apply thread's is open, so the read buffer holds
  what its last batch committed (today's clause takes `authOwn` without `T`, false inside a batch).
In the other modes today's. -/
def AonDraft.auth.authReadTxOk (tx : GoInterface) (R : IProp GF) (M : auth.AuthMode)
    (γc : auth.AuthBkNames) : IProp GF :=
  match M with
  | .on γa => iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗ ∃ Hs : auth.AuthState → IProp GF,
      □ (∀ q : Qp, {{ R ∗ auth.authCur γc q }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
        {{ RET #(); ∃ st : auth.AuthState, Hs st ∗ auth.authSnap (.on γa) st ∗ auth.authCur γc q }}) ∗
      □ (∀ (i : Nat) (q : Qp),
        {{ R ∗ auth.authPubLbM (.on γa) i ∗ auth.authCur γc q }}
          (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
        {{ RET #(); ∃ st : auth.AuthState, Hs st ∗ auth.authSnapFrom (.on γa) i st ∗
            auth.authCur γc q }}) ∗
      □ (∀ hs : List auth.AuthState,
        {{ R ∗ auth.authWTok γc ∗ auth.authHistHalf γa hs }}
          (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
        {{ RET #(); ∃ st : auth.AuthState, Hs st ∗ auth.authSnap (.on γa) st ∗ auth.authWTok γc ∗
            auth.authHistHalf γa hs ∗ ⌜hs.getLast? = some st⌝ }}) ∗
      auth.authTxReads ti R Hs)
  | _ => Perennial.EtcdGrove.auth.authReadTxOk tx R M

/-- **`authBackendOk`, redefined**: `ReadTx()` returns such a transaction. -/
def AonDraft.auth.authBackendOk (be : GoInterface) (R : IProp GF) (M : auth.AuthMode)
    (γc : auth.AuthBkNames) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (tx : GoInterface), RET #tx; AonDraft.auth.authReadTxOk tx R M γc }}))

instance AonDraft.auth.authBackendOk_persistent (be : GoInterface) (R : IProp GF)
    (M : auth.AuthMode) (γc : auth.AuthBkNames) :
    Persistent (AonDraft.auth.authBackendOk (GF := GF) be R M γc) := by
  unfold AonDraft.auth.authBackendOk; infer_instance

/-- **`beP`, redefined** (decision 3; what `beMu` guards at `q`): in `on γa`, the backend's field at
half the fraction, the share of the current backend's name, its guarded contract and the currency
at `q` (readers get a part; `Recover`, under the write lock, all of it). In the other modes today's.
(`authInv` is read with this `beP` and `AonDraft.auth.revFresh`.) -/
def AonDraft.auth.beP (st : Loc) (R : IProp GF) (M : auth.AuthMode) (q : Qp) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (be : go_etcd_io.etcd.server.v3.auth.AuthBackend) (γc : auth.AuthBkNames),
      auth.aF go!"be" st ↦{DFrac.own q.half} be ∗ auth.authBkCur γa q.half γc ∗
      AonDraft.auth.authBackendOk be R (.on γa) γc ∗ auth.authCur γc q)
  | _ => Perennial.EtcdGrove.auth.beP st R M q

/-- **`revFresh`, redefined** (decision 2): today's, with **half** the published index's authority
(`authPubQ γa ½`; the realization holds a quarter, the apply thread a quarter, `authPubTok`). -/
def AonDraft.auth.revFresh (M : auth.AuthMode) (r : w64) : IProp GF :=
  match M with
  | .on γa => iprop(∃ p : Nat, auth.authPubQ γa (1 : Qp).half p ∗
      (∃ sp : auth.AuthState, auth.authStateAt γa p sp) ∗
      (∃ (j : Nat) (s : auth.AuthState), auth.authStateAt γa j s ∗ ⌜p ≤ j ∧ uint.nat r = s.revision⌝) ∗
      (∃ b : Bool, ghostVar γa.fen (1 : Qp).half.half b ∗
        ∃ (j : Nat) (s : auth.AuthState), auth.authStateAt γa j s ∗ ⌜p ≤ j ∧ b = s.enabled⌝) ∗
      ∃ v : GoMap × Nat, ghostVar γa.fca (1 : Qp).half.half v ∗
        ∃ (s : auth.AuthState) (j' : Nat) (s' : auth.AuthState), auth.authStateAt γa v.2 s ∗
          auth.authStateAt γa j' s' ∗ ⌜p ≤ j' ∧ auth.permView s = auth.permView s'⌝)
  | _ => iprop(True)

/-! ### `Recover` and `setRevision`: one spec each over the mode (decision 5) -/

/-- What `Recover` takes besides the store's resources: in `on γa`, the new backend's write token
and whole currency and the apply thread's share of the old backend's name `γc₀`. -/
def auth.recoverIn (M : auth.AuthMode) (γc₀ γc : auth.AuthBkNames) : IProp GF :=
  match M with
  | .on γa => iprop(auth.authWTok γc ∗ auth.authCur γc 1 ∗ auth.authBkCur γa (1 : Qp).half γc₀)
  | _ => iprop(True)

/-- What `Recover` gives back: in `on γa`, the new backend's write token, the share of its name, and
the old backend's whole currency (for its release, decision 3c). -/
def auth.recoverOut (M : auth.AuthMode) (γc₀ γc : auth.AuthBkNames) : IProp GF :=
  match M with
  | .on γa => iprop(auth.authWTok γc ∗ auth.authBkCur γa (1 : Qp).half γc ∗ auth.authCur γc₀ 1)
  | _ => iprop(True)

/-- The read state's facts: in `on γa`, it is the caught-up history's last, `stI`, and fits the
cache; in the other modes nothing is appended (`N = []`) and every state of the mode fits. -/
def auth.recoverFit (M : auth.AuthMode) (hs N : List auth.AuthState) (stI : auth.AuthState) :
    IProp GF :=
  match M with
  | .on _ => iprop(⌜(hs ++ N).getLast? = some stI ∧ auth.permsFit stI⌝)
  | M => iprop(⌜N = []⌝ ∗ □ (∀ s : auth.AuthState, auth.authSnap M s -∗ ⌜auth.permsFit s⌝))

/-- **`setRevision(rev)`, one spec** (decision 5): from the pending authority at `hs ++ N`
(`Recover`'s case: `N` caught up before, `opt = []`) or the whole authority (`AuthEnable`'s case,
inside a batch: `N = []`, the lock's share, `opt` the one state appended here), the latest state
moved to the last of `hs ++ N ++ opt`, whose revision the atomic gets. -/
abbrev AonDraft.auth.authStore.setRevision.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (rev : w64) (hs N opt : List auth.AuthState)
    (stl : auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.authInv st R M ∗ auth.authOwnPM M hs N ∗
      (if opt.isEmpty then iprop(True) else auth.authLockShare M (hs ++ N)) ∗
      (□ ∀ x, ⌜x ∈ opt⌝ -∗ auth.capNext M (hs ++ N) x) ∗
      ⌜auth.histLast M (hs ++ N ++ opt) stl ∧ uint.nat rev = stl.revision ∧ opt.length ≤ 1 ∧
        (N ≠ [] → opt = []) ∧
        (∀ x ∈ opt, (M.isOn = true → M ≠ .any → auth.permKeysOk x) ∧
          (M = .off → x.enabled = false))⌝ }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
      go!"setRevision")) (Val #rev))
  {{ RET #(); auth.authOwn M (hs ++ N ++ opt) ∗
      (if opt.isEmpty then iprop(True) else auth.authLockShare M (hs ++ N ++ opt)) }}

/-- **`as.Recover(be)`, one spec over the mode** (decision 5; candidate (ii) as its `on` case;
today's `Recover.spec` without its unconditional append, which the tie forbids, and without the
write contract, as `Recover` writes nothing): the new backend `be` with its contract in the mode
(in `on γa` the guarded one at `γc`, its token and whole currency `recoverIn`, whose currency
`Recover` puts in `beP` with `be`, taking the old one's out); the store's user's half of the field
(`be0 ↦ be`). `Recover` swaps the backend under `beMu`, reads `be` (in `on γa`, the latest clause:
`T` and the history's half, `stI`), stores its revision (the latest state moves to `stI`) and sets
the flag and the cache from it: the authority at `hs ++ N` with the halves **tied** (`authOwnT`;
today's post has untied halves, finding 3). -/
abbrev AonDraft.auth.authStore.Recover.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (hs N : List auth.AuthState)
    (stI : auth.AuthState) (be : GoInterface) (γc₀ γc : auth.AuthBkNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.authInv st R M ∗ auth.authOwnPM M hs N ∗
      (∃ be0 : go_etcd_io.etcd.server.v3.auth.AuthBackend,
        auth.aF go!"be" st ↦{DFrac.own (1 : Qp).half} be0) ∗
      auth.enabledHalf st M ∗ auth.cacheHalf st M ∗ auth.tpAdmin st M ∗ R ∗
      ⌜be ≠ GoInterface.nil⌝ ∗ AonDraft.auth.authBackendOk be R M γc ∗
      auth.recoverIn M γc₀ γc ∗ auth.recoverFit M hs N stI }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
      go!"Recover")) (Val #be))
  {{ RET #(); auth.tpAdmin st M ∗ R ∗ auth.aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗
      auth.authOwnT st M (hs ++ N) ∗ auth.recoverOut M γc₀ γc }}

/-- **Publication, redefined** (`authPublishM`, decision 2): in `on γa`, for the current backend's
token and lifecycle, the publication quarter beside the authority and the tie (from the redefined
`revFresh`'s half and `authBkLife`'s publish clause; `authPublishM_of_authInv`, restated, not
drafted). -/
def AonDraft.authPublishM (M : auth.AuthMode) (stl : Loc) : IProp GF :=
  match M with
  | .on γa => iprop(□ ∀ (hs : List auth.AuthState) (γc : auth.AuthBkNames) (K : IProp GF),
      ⌜hs ≠ []⌝ -∗ auth.authBkLife γa γc K -∗ auth.authOwn (.on γa) hs -∗ auth.authWTok γc -∗
      auth.authPubTok γa -∗ auth.tieRes stl (.on γa) hs ={⊤}=∗
      auth.authOwn (.on γa) hs ∗ auth.authWTok γc ∗ auth.authPubTok γa ∗
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
- **`Recover`'s own read** needs one `R`: lent by the clause against the new backend's read token.
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

/-- The tracked buckets but the auth ones. -/
def restNonAuth (n : GoString) : Prop :=
  n ≠ go!"auth" ∧ n ≠ go!"authUsers" ∧ n ≠ go!"authRoles"

/-- **The client's half of the tracked buckets in `S`** (decision 1: `rbOwn` split by bucket set;
a backend-level change, the tracked-bucket token `γ.rbk` becoming a map per bucket): the writer's
contents hold `r` at the tracked buckets of `S`. Opaque in the draft; its law below. -/
opaque backend.rbOwnIn (γ : backend.BNames) (S : GoString → Prop)
    (r : GMap GoString backend.BktData) : IProp GF := iprop(True)

/-- **The split** (the backend-level change's law; statement only). -/
theorem backend.rbOwn_split_in (γ : backend.BNames) (S : GoString → Prop)
    (r : GMap GoString backend.BktData) :
    backend.rbOwn (GF := GF) γ r ⊣⊢ backend.rbOwnIn γ S r ∗ backend.rbOwnIn γ (fun n => ¬ S n) r := by
  sorry

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

/-- **The snapshot clause** (trusted; persistent, at the store's `R`): a backend `d` the apply
thread opened, its hook frozen, its tracked auth buckets `r` holding `st` (`authBucketsAt`), the
lock's share of the history at `st` (deposited, as at boot: `st` is the history's last, so
recorded and at an index no smaller than the published one), its open share `authOpenQ`: schema's
auth backend `abl` over it meets, for fresh names `γc`, the guarded read contract at `R`, the write
contract at its hook and at every schema auth backend on it (`authWAtHook`), with the write token,
the whole currency and the lifecycle (`authBkLife`, its realization keeping the open share); one
`R` lent against the backend's read token; the client's half of the **non-auth** tracked buckets
back (decision 1). -/
def authSchemaSnap (γa : auth.AuthNames) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
      (r : GMap GoString backend.BktData) (st : auth.AuthState),
    ⌜lg ≠ null⌝ -∗ ⌜authBucketsAt st r⌝ -∗ ablOn abl d.be lg -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
    backend.rbOwn d.γB r -∗ mvcc.bkRTx d.γB d.P d.be -∗ backend.bOpen d.γB authOpenQ -∗
    auth.authLockI (.on γa) st -∗
    |==> ∃ γc : auth.AuthBkNames,
      AonDraft.auth.authBackendOk (authBkIface abl) R (.on γa) γc ∗ auth.authCur γc 1 ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) Pk #f (auth.authWTok γc) ∗
      authWAtHook γa d γc ∗ auth.authWTok γc ∗
      auth.authBkLife γa γc (backend.bOpen d.γB authOpenQ) ∗
      R ∗ (R -∗ mvcc.bkRTx d.γB d.P d.be) ∗ backend.rbOwnIn d.γB restNonAuth r)

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
authority); `actualMaxReaders` copies of `R`; the constructor's critical section, whose `Post`
gives back the open share, the hook and the client's half of the **non-auth** tracked buckets
(decision 1: the auth buckets' write authority stays with the realization); and the snapshot clause
at `R`.

Today's five refutations, against this text: (1) the latest clause takes `T`; (2) the published
index's authority is shared with the realization, publication needs `T`; (3) no `rbOwn` of the auth
buckets comes back; (4) `Cu`/`T` stand for an open share the realization keeps until both are
surrendered; (5) `T` and `Cu` are functions of `γc`, which `beP` and the apply thread share. -/
def AonDraft.authSchemaSrv : IProp GF :=
  iprop(□ ∀ (γa : auth.AuthNames) (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
      (r : GMap GoString backend.BktData),
    ⌜lg ≠ null⌝ -∗
    ⌜(r.lookup go!"auth").getD ∅ = ∅ ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
      (r.lookup go!"authRoles").getD ∅ = ∅⌝ -∗
    ablOn abl d.be lg -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.bOpen d.γB qo -∗
    backend.bOpen d.γB authOpenQ -∗
    backend.plHook d.γB func.nil -∗ ownToks d.γB.wb 2 -∗ backend.rbOwn d.γB r -∗
    auth.authLockI (.on γa) auth.bootState -∗ auth.authPubQ γa (1 : Qp).half 0 -∗
    |==> ∃ (R P : IProp GF) (f : val) (Pre Q Post : IProp GF) (γc : auth.AuthBkNames),
      AonDraft.auth.authBackendOk (authBkIface abl) R (.on γa) γc ∗ auth.authCur γc 1 ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) P f (auth.authWTok γc) ∗
      authWAtHook γa d γc ∗
      □ ({{ auth.authWTok γc }} (App (Val #(methods
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
          go!"CreateAuthBuckets" #abl)) (Val #())) {{ RET #(); auth.authWTok γc }}) ∗
      auth.authWTok γc ∗ auth.authPubTok γa ∗
      auth.authBkLife γa γc (backend.bOpen d.γB authOpenQ) ∗
      mvcc.csContract P f Pre Q Post ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), R) ∗
      (Post -∗ backend.bOpen d.γB qo ∗ backend.plHook d.γB func.nil ∗
        backend.rbOwnIn d.γB restNonAuth (authBucketsAfter r)) ∗
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
(`authWAtHook`), the admin steps at any hook (`authStepsAny`) and the provider's admin share.
(Boot's form adds the token rights' empty authority, `ghostMapAuth γa.fresh`, as today's.) -/
def AonDraft.authApplyResPre (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState)
    (d : mvcc.KBReal) (RD : IProp GF) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f0 : val) (γc : auth.AuthBkNames)
      (be : GoInterface) (b : Nat),
      auth.authOwn (.on γa) hs ∗ authFuelB hs b ∗ auth.tieRes stl (.on γa) hs ∗
      auth.authWBackendOk be (.on γa) P f0 (auth.authWTok γc) ∗ auth.authWHeld γa γc ∗
      auth.authPubTok γa ∗ auth.authBkLife γa γc (backend.bOpen d.γB authOpenQ) ∗
      authWAtHook γa d γc ∗ authStepsAny stl γa RD ∗ auth.tpAdmin stl (.on γa) ∗
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
image's committed log `A'` extending `A`, the new backend `dn` opened with its hook frozen, its
tracked auth buckets `r` holding `A'`'s state, its open share for the realization, and the snapshot
clause at the store's `R`: after `Recover`, the store on the new backend (`authBeOn`), the apply
thread's auth resource on it at `A'`'s state, the non-auth buckets' half and the read token back,
and **the old backend's open share** (after an update: its release, for the close goroutine;
decision 3c). -/
abbrev authRecoverOn.spec : Prop :=
  ∀ (ast abl lg : Loc) (dO dn : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
    (r : GMap GoString backend.BktData) (γa : auth.AuthNames) (R RD : IProp GF) (E : apply.AEnv GF)
    (γr : ReadNames) (A A' : List EntryModel) (sa : auth.AuthState),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      authBeOn ast dO.be ∗ AonDraft.authApplyResPre (.on γa) ast sa dO RD ∗
      auth.authInv ast R (.on γa) ∗ authSchemaSnap γa R ∗
      authHistTie E γr srvAuthSt0 ∗ srvRLogLb γr.raft A' ∗
      ⌜A <+: A' ∧ sa = srvAuthAtLog γr.kv srvAuthSt0 A ∧ A'.length < 2 ^ 61⌝ ∗
      ⌜lg ≠ null⌝ ∗ ablOn abl dn.be lg ∗
      backend.isBackend dn.γB dn.P W Pk dn.be ∗ backend.plHookRO dn.γB f ∗ ⌜f ≠ func.nil⌝ ∗
      backend.rbOwn dn.γB r ∗ mvcc.bkRTx dn.γB dn.P dn.be ∗ backend.bOpen dn.γB authOpenQ ∗
      ⌜authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A') r⌝ }}
    (App (Val (ast @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
      go!"Recover")) (Val #(authBkIface abl)))
  {{ RET #(); |==> (authBeOn ast dn.be ∗
      AonDraft.authApplyResPre (.on γa) ast (srvAuthAtLog γr.kv srvAuthSt0 A') dn RD ∗
      backend.rbOwnIn dn.γB restNonAuth r ∗ mvcc.bkRTx dn.γB dn.P dn.be ∗
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
theorem authRecoverOn_glue (hRec : AonDraft.auth.authStore.Recover.spec (GF := GF) (hG := hG)) :
    authRecoverOn.spec (GF := GF) (hG := hG) := by
  intro ast abl lg dO dn W Pk f r γa R RD E γr A A' sa hM
  simp only [AonDraft.authApplyResPre]
  iintro %Φ ⟨#Hpkg, Hbeon, Hres, #Hinv, #Hsnap, #Htie, #HA', %Hp, %Hlg, #Habl, #HisB, #Hhk,
    %Hf, Hrb, Hrt, HbO, %Hbk⟩ HΦ
  obtain ⟨hpre, hsa, hlen⟩ := Hp
  obtain ⟨hk, hfit, hsmall, hrev⟩ := srvHist_wf γr.kv A' hlen
  icases Hres with ⟨%hs, %P0, %f0, %γc₀, %be, %b, Hown, Hfu, Htr, -, HTh, Hpub,
    #Hlife, -, #Hsteps, Htp, %Hlast⟩
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
  imod Hret0 $$ [HT Hpub] with ⟨⟨%st0, Hlk⟩, Hrtd⟩
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
  imod Hsn $$ %lg %abl %dn %W %Pk %f %r %(srvAuthAtLog γr.kv srvAuthSt0 A') [] [] Habl HisB Hhk
      [] Hrb Hrt HbO Hlk
    with ⟨%γc, #HokH, HCu, #HwR, #HwH, HT', #Hlife', HR, HRb, Hrb⟩
  · ipureintro; exact Hlg
  · ipureintro; exact Hbk
  · ipureintro; exact Hf
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
  ihave Hrt := HRb $$ HR
  imodintro
  iframe Hrb Hrt HoO
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
  ipureintro; exact hcl

end glue

/-! ## The install with auth on (`specSnapOn`) and its caller -/

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
    auth.authInv ast R (.on γa) ∗ authSchemaSnap γa R ∗ ⌜RD = auth.authRd ast R (.on γa)⌝)

instance srvAuthSnapOk_persistent (s : Loc) (γa : auth.AuthNames) (RD : IProp GF) :
    Persistent (srvAuthSnapOk (GF := GF) s γa RD) := by
  unfold srvAuthSnapOk; infer_instance

/-- **The image certificate in the cluster's mode** (decision 7, `srvSnapRO`'s certificate by mode;
review round 1's F5): `srvImageOn` in `on`, today's `srvImage` otherwise (by `rfl`). In the merge,
with #7-on, the one `srvImage` over the mode. -/
def srvImageM (M : auth.AuthMode) (γ : SrvRaft) (i : w64) (D : backend.Data) : IProp GF :=
  match M with
  | .on _ => srvImageOn γ i D
  | _ => srvImage γ i D

theorem srvImageM_off (γ : SrvRaft) : srvImageM (GF := GF) .off γ = srvImage γ := rfl

/-- **The rest buckets' owner, redefined over the mode** (decision 1, "the mode-on `srvRest` holds
the auth buckets at the log's auth state"): in `on`, the client's half of the **non-auth** tracked
buckets at the rest model (the auth buckets' write authority is the auth realization's, their
contents the history's last state, which `authHistTie`/`kvRunAtOn` make the log's auth state;
finding 5's gap, the rest model's auth buckets staying `authBoot`, no longer reaches `srvRest`); in
the other modes today's `srvRestOwn` (`rbOwn` of every tracked bucket). `srvRestOwnH`, `E.RO`'s
equation in `srvSnapRO`/`specSnap`, takes the mode with it. -/
def AonDraft.srvRestOwn (M : auth.AuthMode) (γB : backend.BNames) (c : Loc) (r : apply.RestM) :
    IProp GF :=
  match M with
  | .on _ => iprop(backend.rbOwnIn γB restNonAuth r.bk ∗ membership.clusterMem c r.mem)
  | _ => Perennial.EtcdGrove.srvRestOwn γB c r

theorem AonDraft.srvRestOwn_off (γB : backend.BNames) (c : Loc) :
    AonDraft.srvRestOwn (GF := GF) .off γB c = Perennial.EtcdGrove.srvRestOwn γB c := rfl

/-- **`srvSnapRO`'s two mode-dependent clauses, redefined** (decision 7 and 8): `srvSnapRO` is
today's with `snapDirInv ss γd (srvImage γr.raft.raft) …` replaced by `snapDirInv ss γd (srvImageM
E.authMode γr.raft.raft) …`, `E.RO = srvRestOwnH d.γB cl …` by its mode-indexed owner
(`AonDraft.srvRestOwn E.authMode`), and, beside `□ (⌜E.authMode = off⌝ → authRecoverOk ast)`, the
mode-`on` row `□ ∀ γa, ⌜E.authMode = .on γa⌝ → srvAuthSnapOk s γa E.RD` (the gated `Recover` facts
of decision 5). Drafted as the delta, the rest of the bundle unchanged. -/
def AonDraft.srvSnapROAuth (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γd : GName)
    (ss : Loc) (γt : GName) : IProp GF :=
  iprop(inv snapDirN (snapDirInv ss γd (srvImageM E.authMode γr.raft.raft) (srvSnapRm γt γr)) ∗
    □ (∀ γa : auth.AuthNames, ⌜E.authMode = .on γa⌝ → srvAuthSnapOk s γa E.RD))

/-- **`srvSnapApplied` with auth on**: the server's row in the mode, the applier at the image's
auth state (the state after `A'`). -/
def srvSnapAppliedOn (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (R : mvcc.Log) (A' : List EntryModel)
    (ss : Loc) (bp : GoString) (γt : GName) (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds)
    (idm : w64) (lp al ast cl : Loc) : IProp GF :=
  iprop(∃ (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (E' : apply.AEnv GF) (b' : GoInterface)
      (st' : ApplyState) (d' : mvcc.KBReal) (x' : apply.ApplyKV) (cs' : Loc) (L : List w64),
    ⌜beSucc γ E γ' E' ∧ E'.γ.kb = some d' ∧ d'.cm = false ∧ d'.P = d.P ∧
      E'.RO = srvRestOwnH d'.γB cl (srvObjsOn al ast lp cl d'.be) ∧
      loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' ∧
      x'.log = [[], []] ++ R ∧ x'.chain = apply.alarmChain E.authOn false false ∧
      (∀ f, (netRh γn).member f → f ≠ idm → f ∈ L)⌝ ∗
    isServerM true s γ' ci TM' E' ρ γr ∗
    epAppliedIAddr ep ↦ sv.Metadata'.Index' ∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' ∗
    epDiskSnapAddr ep ↦ sv.Metadata'.Index' ∗ epMemSnapAddr ep ↦ sv.Metadata'.Index' ∗
    epConfState ep cs' ∗ csOptA cs' DFrac.discard sv.Metadata'.ConfState' ∗
    applyThread γ' st' ∗ applyBackend γ' ci b' ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
    srvApplyKVOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') ∗ srvRest E' γr A' ∗ srvKVCloser s E' ∗
    backend.isStopChans d'.γB d'.be ∗ backend.bOpen d'.γB (1 : Qp).half ∗
    monoNatAuthOwn γt 1 (uint.nat sv.Metadata'.Index') ∗
    backend.pathOwn bp ∗
    trLive γn t c L ∗
    (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E'.s E'.γ))

/-- **`s.applySnapshot(ep, ap)` with a non-empty snapshot, auth on** (Q4: a standalone triple
beside `specSnap`; how it is packaged with `spec`/`specSnap` is open): `specSnap`'s statement with
the mode `on γa` (`hon` for `hoff`), the server's and the applier's rows in the mode
(`isServerM true`, `srvApplyKVOn` at the applied log's auth state), the image's auth buckets
at the state after its log `A'` (`hauthI` for `hauthb`; `A <+: A'` and the committed `A'`, the
catch-up's), `Recover`'s premise the store's invariant at the server's `E.RD` with the snapshot clause
(`authSchemaSnap`, for `authRecoverOk`), the apply contract in the mode. After: `srvSnapAppliedOn`,
the applier at the image's auth state.

Read under the merge's redefinitions (review round 1's F4): `srvApplyKVOn`'s auth part,
`authApplyResB (.on γa)`, is `AonDraft.authApplyResB`'s form (the fuel at a base, the token's
retirement, the hook clause), which `Recover`'s glue needs and gives back; today's form
(`authOwnFu`, no retirement) cannot be carried over a jump (the plan note's findings 1 and 2). -/
abbrev EtcdServer.applySnapshot.specSnapOn : Prop :=
  ∀
    (s ep ap sn : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai at0 dsi : w64) (nc : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss hk : Loc)
    (hi : uint.Z ai < uint.Z sv.Metadata'.Index')
    (d : mvcc.KBReal) (D : backend.Data) (lgh : Loc)
    (hkb : E.γ.kb = some d)
    -- (question 5's core stage, part (1); Q5-4, review round 16's M1) the store's backend does not
    -- compact: no restore in compaction mode (M2's apply side, 2026-10-31, the user's (a): an interim
    -- restriction, `srvEnvOk` now giving `d.cm = E.cmp`; the caller's mode off gives it)
    (hcm : d.cm = false)
    (hdbo : storage.dbOpensOk) (hsop : storage.snapOpensOk)
    (hP : d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧ ciKeys d.P ∧ storage.hooksParams d.P)
    (hcfgl : cfg.Logger' ≠ null) (hmmap : storage.openMmapOk cfg)
    (tI : w64) (hmeta : metaIs D (sv.Metadata'.Index', tI))
    (st : ApplyState) (b : GoInterface)
    (hle : uint.Z (ciEff γ st.k) ≤ uint.Z sv.Metadata'.Index')
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (hRO : E.RO = srvRestOwnH d.γB cl (srvObjsOn al ast lp cl d.be))
    (hlease : ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅)
    (hwq : E.γ.watchQ = true)
    (R : mvcc.Log) (hpre : x.log <+: [[], []] ++ R) (hRok : mvcc.restoreLogOk R)
    (hkI : mvcc.keyImage ([[], []] ++ R) D) (hbr : mvcc.bridgeParams d.P)
    -- (the lease-revoke plan, 2026-10-31) the `Lease` bucket in the table, tracked, no hook keys
    -- (the boot backend's, `bootOk`; the new backend's parameters are the old one's)
    (hlp : mvcc.leaseParams d.P)
    (γp : GName) (hrbw : receiptBound GF ≤ backend.wbInit - 6)
    (stp : Loc) (γd γt : GName) (img : w64 → backend.Data → IProp GF) (nt : Nat)
    (hstp : storage.storageSnap stp ss) (hnt : nt ≤ uint.nat sv.Metadata'.Index')
    (halarm : ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅)
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
    -- (auth on) the rest model's buckets but the auth ones (the rest model does not model the
    -- admin writes: its auth buckets stay `authBoot`, a finding, see the file's notes)
    (hA' : (∀ n, n ≠ go!"auth" → n ≠ go!"authUsers" → n ≠ go!"authRoles" →
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk.lookup n =
        (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D))).lookup n) ∧
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI)
    -- (auth on, `snapRecv_imageOn`'s) the image's auth buckets hold the state after `A'`, which
    -- extends the applied log `A` (whose state is the store's latest, `sa`), below raft's bound
    (hauthI : authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A') (backend.rbData d.P D))
    (hpreA : A <+: A') (hlenA' : A'.length < 2 ^ 61)
    -- (S8d's named premise, S-j1's: `NewServer`'s environment, kept by `beSucc`) the auth store's
    -- contract mode is `.on γa`, the mode `authApplyOkM` gives the store's contract in
    (γa : auth.AuthNames) (hon : E.authMode = .on γa)
    -- (2026-11-01, J8a-1, item 8) the payload's two-receive `notifyc` (`rnApSnap`'s), before its
    -- first receive (until then a unit bag)
    (γnc : NotifyNames),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       isServerM true s γ ci TM E ρ γr ∗
       taSnapshotAddr ap ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
       taNotifycAddr ap ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
       epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epDiskSnapAddr ep ↦ dsi ∗
       srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
       srvCfgAddr s ↦□ cfg ∗ structFieldRef EtcdServer go!"snapshotter" s ↦□ ss ∗
       structFieldRef EtcdServer go!"beHooks" s ↦□ hk ∗
       snap.isSnapshotter ss ∗ backend.fileHolds (snap.snapDBPath ss sv.Metadata'.Index') D ∗
       backend.pathOwn (config.backendPathOf cfg.DataDir') ∗
       (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
       storage.isBackendHooks hk
         ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #ci⟩ lgh ∗
       applyThread γ st ∗ applyBackend γ ci b ∗
       srvApplyKVOn s E ρ.wait x (srvAuthAtLog γr.kv srvAuthSt0 A) ∗ srvRest E γr A ∗
       lease.lessorInv lp E.γ.leases ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
       srvKVCloser s E ∗
       (∃ (wsl : Loc) (γw0 : mvcc.WsNames), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
        mvcc.isWatchableStore wsl E.s γw0) ∗
       mvcc.certOk E.γ ([[], []] ++ R) ∗
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
       backend.isStopChans d.γB d.be ∗ backend.bOpen d.γB (1 : Qp).half ∗
       -- (auth on: Q2's candidate (ii)) the store's invariant at the server's read resource
       -- `E.RD`, the snapshot clause at it (carried from `NewServer`'s generalized premise), the
       -- image's committed log
       srvAuthSnapOk s γa E.RD ∗ srvRLogLb γr.raft A' ∗
       -- (S8d's named premises, S-j1's: `NewServer`'s contracts of the stores on whichever backend)
       alarmApplyOk al ∗ authApplyOkM (.on γa) ast E.RD ∗ lessorApplyOk lp ∗ clusterApplyOk cl ∗
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
    {{ RET #(); srvSnapAppliedOn s ep sv γ ci E ρ γr d R A' ss (config.backendPathOf cfg.DataDir') γt γn t c rs idm lp al ast cl ∗
      notifyRcvN γnc 1 }}

/-- **`s.applyAll(ep, ap)` on a snapshot payload, auth on** (the caller of
`applySnapshot.specSnapOn`; `applyAll.specSnap`'s statement in the mode `on γa`: the server's,
the applier's and the KV's rows in the mode at the applied log's auth state `sa`, the start's
chain the mode-on one, and the store's snapshot clause, `srvAuthSnapOk`; after, at the image's
auth state). Read under `srvSnapRO`'s image certificate in the mode (review round 1's F5:
`srvSnapOwn`'s `srvSnapRO` holds `snapDirInv … (srvImage γr.raft.raft)`, the mode-off certificate,
false of an auth-on cluster's images; in the merge `srvImageM E.authMode`, `srvImageOn` in the
mode `on`, from which `snapRecv_imageOn` gives `specSnapOn`'s `hauthI`/`hkI`), and under
`authApplyResB`'s redefinition as `specSnapOn` is. -/
abbrev EtcdServer.applyAll.specSnapOn : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (ep ap : Loc) (es : GoSlice) (sn : Loc)
    (sv : SnapshotM) (rac nc : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (A : List EntryModel) (mst : Loc) (γs : MemStorNames) (γp : GName)
    (γnc : NotifyNames) (w : Nat) (nid : w64) (q : Qp) (γn : RNNames) (rt : w64) (n : Nat)
    (γa : auth.AuthNames) (sa : auth.AuthState),
  E.authMode = .on γa →
  -- the snapshot past the applied index, below `2^61`, at least the boot log
  uint.Z ai < uint.Z sv.Metadata'.Index' → uint.Z sv.Metadata'.Index' < 2 ^ 61 →
  (γr.raft.raft.boot.length : Int) ≤ uint.Z sv.Metadata'.Index' →
  -- the applied log `A` through `ai`, the consistent index at most the applied one
  uint.Z ai = A.length → uint.Z (ciEff γ st.k) ≤ uint.Z ai →
  -- a fresh cluster's start (`snapRecv_image`'s), compaction off
  γr.raft = ⟨γr.raft.raft, [], W64 0⟩ → γr.kv.c0 = W64 0 →
  γr.kv.ch0 = apply.alarmChain true false false → γr.kv.log0 = [[], []] → E.cmp = false →
  -- the batch's term good for a log at least the snapshot's (the merge's guard)
  γn.node = γr.raft.raft → uint.nat sv.Metadata'.Index' ≤ n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM true s γ ci TM E ρ γr ∗ isServerApplyAll s γr ∗ srvMemberIDAddr s ↦□ nid ∗
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
      srvApplyKVOn s E ρ.wait x sa ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      srvWTPool E γp ∗ srvWTTaken γp w ∗ kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      srvApRes s γr A ∗ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗
      rnWalTok (srvRAddr s) q ∗
      -- the snapshot path's resources (`srvSnapRO`'s configuration rebuild over
      -- `isServerApplyAll`'s two fields)
      srvSnapOwn s ci E γr ai ∗
      -- (auth on) the store's invariant at the server's `E.RD` and the snapshot clause (Q2's candidate (ii)),
      -- carried from `NewServer` as `#HmetaSnap` is
      srvAuthSnapOk s γa E.RD ∗
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
        ⌜beSucc γ E γ' E'⌝ ∗ isServerM true s γ' ci TM' E' ρ γr ∗ srvApRes s γr A' ∗
        srvRLogLb γr.raft A' ∗
        epAppliedIAddr ep ↦ sv.Metadata'.Index' ∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' ∗
        epConfState ep cs' ∗ epCsAt ρ.raft A' cs' ∗
        srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) ∗ applyThread γ' st' ∗
        applyBackend γ' ci b' ∗ ciApplying ci a t ∗
        srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗
        srvAppliedOwn γr sv.Metadata'.Index' ∗ appliedAtLeast γr sv.Metadata'.Index' ∗
        srvWTTaken γp w ∗
        (∃ x' : apply.ApplyKV, srvApplyKVOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') ∗
          appliedLogAt γr sv.Metadata'.Index' x'.log ∗
          kvAppliedOn γr.raft γr.kv srvAuthSt0 A' x' (srvAuthAtLog γr.kv srvAuthSt0 A') ∗ srvRest E' γr A') ∗
        (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E'.s E'.γ) ∗ rnWalTok (srvRAddr s) q ∗
        srvSnapOwn s ci E' γr sv.Metadata'.Index' ∗
        ⌜loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' ∧
          A <+: A' ∧ (γr.raft.pre ++ A').length = uint.nat sv.Metadata'.Index' ∧
          lastTermIs A' sv.Metadata'.Term'⌝ }}

/-- **The glue at `run`: the applied log's auth state** (what `specSnapOn`'s applied auth state and
`applyAll.specSnapOn`'s `kvAppliedOn` take, from `applyResOn`'s `kvRunAtOn`): the KV row's model
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

/-- **`run`'s auth-on snapshot-payload job** (`EtcdServer__run.lean` ~:1413, statement only, **a
schematic outline**: it does not yet take what `applyAll.specSnapOn` needs beyond `applyResOn`
(review round 3's C: the fresh start's facts `γr.raft = ⟨_, [], 0⟩`, `c0 = 0`, `ch0`, `log0`,
`E.cmp = false`, `|boot| ≤ i`, the term bound; the payload's `notifyc`, `rnAdvChan`, `rnRtOk`; the
meta reads), which J8b's mode-off job takes from `isServerRun` and the payload; the auth-on twin
of J8b's mode-off job): from the loop's resources at `A` (`applyResOn`) and the
payload's (`rnApplyTok_recv`'s snapshot branch, at a fresh start), with the store's snapshot clause
(`srvAuthSnapOk`, which `isServerRunOn` does not carry today: a finding, the line `run` needs from
`NewServer`), `applyAll.specSnapOn` gives the loop's resources at the image's log `A'`. Besides
what J8b's mode-off job takes of `isServerRun` (`γr.kv.log0 = [[], []]`, `#HmetaSnap`'s premise,
`|boot| ≤ i`), the mode-on start's chain (`γr.kv.ch0 = alarmChain true false false`) and the
snapshot directory's image in the mode (`srvSnapRO`'s `snapDirInv … (srvImage …)` is the mode-off
certificate: `srvImageOn`, #7-on). On J8b (`snap-j8b`, uncommitted when drafted): `isServerRunOn`
carries `srvMemberIDAddr s ↦□ γn.id` and `srvMetaSnap γ` in both modes, so the free `nid` here
becomes `γn.id` (taken from `isServerRunOn`), the meta premise `srvMetaSnap C.γ` comes from it,
`|boot| ≤ i` from `rnApSnap` (J8b's `rnReadySnap_bootLen`), and the job splits on `C.E.cmp` as
`run_job_snap` does (`run_job_snap_cmp`); `srvAuthSnapOk` joins them as an `isServerRunOn` fact
(decision 8). -/
theorem run_snap_jobOn (hAA : EtcdServer.applyAll.specSnapOn (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (A : List EntryModel) (γa : auth.AuthNames)
    (hM : C.E.authMode = .on γa) (apL : Loc) (sv : SnapshotM) (γs : schedule.SchedNames)
    (γn : RNNames) (nid : w64) (hγn : γn.node = C.γr.raft.raft) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerApplyAll C.s C.γr ∗ srvMemberIDAddr C.s ↦□ nid ∗ schedule.schedRunning γs ∗
        applyResOn C A ∗ srvAuthSnapOk C.s γa C.E.RD ∗
        ⌜(γn.pre ++ A).length < uint.nat sv.Metadata'.Index' ∧
          uint.Z sv.Metadata'.Index' < 2 ^ 61⌝ ∗
        taEntriesAddr apL ↦□ (GoSlice.mk null (W64 0) (W64 0)) ∗
        (∃ sn : Loc, taSnapshotAddr apL ↦□ sn ∗ ownSnapM sn DFrac.discard sv) ∗
        (letI := srvStor (GF := GF) γn.node
         snapshotCert γn.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists)) ∗
        nodeSnapLocal γn.node.cl γn.id sv.Metadata'.Index' }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ ∃ A' : List EntryModel, applyResOn C A' ∗
        srvRLogLb C.γr.raft A' ∗
        ⌜A <+: A' ∧ (γn.pre ++ A').length = uint.nat sv.Metadata'.Index'⌝ }} := by
  sorry

end install

end EtcdGrove
end Perennial
