/-
**The snapshot install with auth on (Draft; `notes/snapshot-auth-on-plan.md`).** Imported by
nothing. Statements top-down, proofs `sorry` but the glue and the ghost lemmas.

1. **The history's catch-up** (Q1 (b), proved): `authHistTie_catchup`, `catchup_list`.
2. **Q3 (b), the image**: `authDataOf`, `authBucketsAt` (over `schema.authBucketsAre`, with the
   revision's `uint64` bound), `authBucketsAt_after` (proved), `imageAtOn`/`dbImageOn`/`srvImageOn`,
   `SnapImageFactsOn`, `snapRecv_imageOn` (sorry), `srvHist_wf` (pure model facts, sorry: to check).
3. **Q2's timing, candidate (ii) "record first"** (auth package): `auth.authOwnP`,
   `auth.authCatchUpFirst` (proved), `auth.curFrac`, `auth.authReadTxOkH`/`authBackendOkH` (the
   read contract guarded by the write token and the backend's currency), `setRevision.specP`,
   `Recover.specP`.
4. **Q2's timing, candidate (i) "announced"**: `auth.authSnapC` (+ `authSnapC_of_snap`, proved),
   `auth.authReadTxOkC`/`authBackendOkC`, `Recover.specC` (statable only under `authSnap`'s
   redefinition).
5. **Q2's premise** (trusted, to be one premise with boot's): `authLockRetire`, `authWAtHook`,
   `authSchemaSnap` (ii), `authSchemaSnapC` (i), `authSchemaSrvG` (boot's premise changed in place:
   its read contract guarded, the boot token's retirement and the snapshot clause added).
6. **The apply thread's auth resource after a jump**: `authFuelB` (the fuel at a base),
   `authFuelB_of_fuel` (proved), `authApplyResOn`.
7. **`Recover` at the install**: `authRecoverOn.spec` and its glue `authRecoverOn_glue` (proved
   from `Recover.specP`, `authSchemaSnap`, `srvHist_wf`).
8. **The install and its callers**: `srvAuthSnapOk`, `srvSnapAppliedOn`,
   `applySnapshot.specSnapOn` (a standalone triple beside `specSnap`), `applyAll.specSnapOn`,
   `kvRunAtOn_sa` (proved), `run_snap_jobOn` (sorry).
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

/-! ## Q2, the timing: candidate (ii), "record first" (the history caught up before `Recover`)

The catch-up appends the skipped states and the image's state `stI` to the history **before**
`Recover`, ghost only, leaving the latest state's ghost variable (`authCurHalf`, tied to the
`revision` atomic by `revCur`) at the applied state: the history may run ahead of the latest
state, which no shared invariant forbids (only the admin side's `authOwnF`/`authOwn` tie the two,
and the admin side is the apply thread, which holds the pending form `authOwnP` instead). So
`stI` is recorded before `Recover` publishes the new backend under `beMu`, and the timing
needs no change to the read contracts (`authSnap` and the verdict lemmas keep their text; the
guards of `authReadTxOkH` are for other reasons, the reviews' F1-F3). `Recover`'s `setRevision` then moves the latest state to `stI`
(`setRevision.specP`). -/

section authDraft
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

/-- **The catch-up, before `Recover`** (candidate (ii); ghost only): with the whole authority at
`hs` and the cap's permission at `hs ++ N` (`authHistTie_catchup`), the states of `N` are
appended to the history (the revision invariant's quarter with it, its cap bound raised to
`hs ++ N`); the admin side keeps the pending authority, the lock's share is at the new last
state `stI` (for the new backend's lock), and `stI` is recorded. -/
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

/-- **A backend's currency is fractional** (`Cu q`, what readers hold a part of). -/
def auth.curFrac (Cu : Qp → IProp GF) : IProp GF :=
  iprop(□ (∀ q1 q2, Cu (q1 + q2) ∗-∗ Cu q1 ∗ Cu q2))

instance auth.curFrac_persistent (Cu : Qp → IProp GF) : Persistent (auth.curFrac Cu) := by
  unfold auth.curFrac; infer_instance

/-- **The read transaction, guarded** (candidate (ii); review round 1's F1): `authReadTxOk` in the
mode `on γa` with its two clauses that claim more than "a recorded state" guarded by what makes
them true of the code:
- **the admin side's latest clause** takes the backend's write token `T` with the history's half
  (`authHistHalf`, which `authOwn` and the pending `authOwnP` both contain): holding `T`, the apply
  thread has no batch transaction open, so the read buffer holds what its last batch committed,
  `hs`'s last (today's clause takes `authOwn` without `T`, and is false inside a batch: `Unlock`'s
  pre is `authOwnF M hs` at the batch's new state, which splits into `authOwn hs ∗` the lock's
  quarter while the buffer still holds the old state, a finding of the review about the boot
  premise, `notes/snapshot-auth-on-plan.md`); `authLockRetire` consumes `T`, so the clause dies
  with its backend (the old one's would otherwise claim `hs ++ N`'s last after the catch-up);
- **the freshness clause** takes a part of the backend's **currency** `Cu q` (a fraction the
  store's `beP` holds with the backend, under the merge's redefinition of `beP`, and readers hold
  under `beMu`'s read lock, `lockedReadTx`): once `Recover` has swapped the backend under the write
  lock it drops the old backend's currency with its `beP`, so a retired backend's freshness clause
  cannot be invoked (it would claim states it never received).
- **every read** (review round 2's F2) takes the currency too: a retired backend is closed by
  `applySnapshot` (in a goroutine), after which its read transaction dereferences a nil bolt
  transaction (`issues/etcd-auth-snapshot-closed-backend-panic.md`), so even "a recorded state" is
  false of it; readers under `beMu` hold `Cu q` through `beP` (ideally `Cu` also carries the
  backend's open share, tying it to `Close`).
`authReadTxOk`'s clause 2 is replaced by the guarded latest clause, which is **not** weaker: it
takes `T`, and its users (`lockedReadTx.specL`, the four `…Permitted.specL` of `auth/Latest.lean`)
must supply it (the apply thread holds it); the readers' clauses take `Cu q`. In the merge both
guards go into `authReadTxOk` for every backend, boot's included (review round 2's S2). -/
def auth.authReadTxOkH (tx : GoInterface) (R : IProp GF) (γa : auth.AuthNames) (T : IProp GF)
    (Cu : Qp → IProp GF) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗ ∃ Hs : auth.AuthState → IProp GF,
    □ (∀ q : Qp, {{ R ∗ Cu q }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : auth.AuthState, Hs st ∗ auth.authSnap (.on γa) st ∗ Cu q }}) ∗
    □ (∀ (i : Nat) (q : Qp),
      {{ R ∗ auth.authPubLbM (.on γa) i ∗ Cu q }}
        (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : auth.AuthState, Hs st ∗ auth.authSnapFrom (.on γa) i st ∗ Cu q }}) ∗
    □ (∀ hs : List auth.AuthState,
      {{ R ∗ T ∗ auth.authHistHalf γa hs }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : auth.AuthState, Hs st ∗ auth.authSnap (.on γa) st ∗ T ∗
          auth.authHistHalf γa hs ∗ ⌜hs.getLast? = some st⌝ }}) ∗
    auth.authTxReads ti R Hs)

/-- The backend whose `ReadTx()` is such a transaction. -/
def auth.authBackendOkH (be : GoInterface) (R : IProp GF) (γa : auth.AuthNames) (T : IProp GF)
    (Cu : Qp → IProp GF) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (tx : GoInterface), RET #tx; auth.authReadTxOkH tx R γa T Cu }}))

instance auth.authBackendOkH_persistent (be : GoInterface) (R : IProp GF) (γa : auth.AuthNames)
    (T : IProp GF) (Cu : Qp → IProp GF) :
    Persistent (auth.authBackendOkH (GF := GF) be R γa T Cu) := by
  unfold auth.authBackendOkH; infer_instance

/-- **`setRevision(rev)` from the pending authority** (candidate (ii)): the atomic set to the
recorded last state's revision, the latest state's ghost variable moved to it. -/
abbrev auth.authStore.setRevision.specP : Prop :=
  ∀ (st : Loc) (R : IProp GF) (γa : auth.AuthNames) (rev : w64) (hs N : List auth.AuthState)
    (stl : auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.authInv st R (.on γa) ∗ auth.authOwnP γa hs N ∗
      auth.authStateAt γa ((hs ++ N).length - 1) stl ∗
      ⌜(hs ++ N).getLast? = some stl ∧ uint.nat rev = stl.revision⌝ }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
      go!"setRevision")) (Val #rev))
  {{ RET #(); auth.authOwn (.on γa) (hs ++ N) }}

/-- **`as.Recover(be)` with auth on, the history caught up** (candidate (ii); over
`setRevision.specP`): the new backend `be` meets the guarded read contract (`authBackendOkH`, at
the store's `R`, its write token `T` and its currency `Cu`, whose whole `Cu 1` `Recover` puts in
`beP` with `be`: read under the merge's `beP`, which holds the backend's currency), the caught-up history's last state `stI` recorded
(so readers of `be` after `beMu.Unlock` read a recorded state) and fitting the cache. `Recover`
puts `be` under `beMu` (the store's user's half of `be` with it: `be0 ↦ be`), reads `stI`
(`RLock` with the history's half), stores its revision (the latest state moves to `stI`) and sets
the flag and the cache to it: the admin side's authority at `hs ++ N` with the halves tied to
`stI` (`authOwnT`, the apply thread's `tieRes`). It writes nothing (no write contract: the
store's user attaches the new backend's after). -/
abbrev auth.authStore.Recover.specP : Prop :=
  ∀ (st : Loc) (R : IProp GF) (γa : auth.AuthNames) (hs N : List auth.AuthState)
    (stI : auth.AuthState) (be : GoInterface) (T : IProp GF) (Cu : Qp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.authInv st R (.on γa) ∗ auth.authOwnP γa hs N ∗
      (∃ be0 : go_etcd_io.etcd.server.v3.auth.AuthBackend,
        auth.aF go!"be" st ↦{DFrac.own (1 : Qp).half} be0) ∗
      auth.enabledHalf st (.on γa) ∗ auth.cacheHalf st (.on γa) ∗
      auth.tpAdmin st (.on γa) ∗ R ∗ ⌜be ≠ GoInterface.nil⌝ ∗ auth.authBackendOkH be R γa T Cu ∗
      T ∗ Cu 1 ∗ auth.curFrac Cu ∗
      auth.authStateAt γa ((hs ++ N).length - 1) stI ∗
      ⌜(hs ++ N).getLast? = some stI ∧ auth.permsFit stI⌝ }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
      go!"Recover")) (Val #be))
  {{ RET #(); auth.tpAdmin st (.on γa) ∗ R ∗ T ∗
      auth.aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗
      auth.authOwnT st (.on γa) (hs ++ N) }}

/-! ## Q2, the timing: candidate (i), "announced" (a state of the cap)

The catch-up stays in `Recover`'s `setRevision` (Q1 (b)'s form, `setRevision.specN`); the
image's state `stI` is announced before `Recover` by the cap's lower bound at the committed log's
history (`authHistTie_catchup`'s `capLb γa (srvHist A')`, no new ghost state). The read contract
must then accept an announced state in `beMu`'s window: `authSnap (.on γa)` is **redefined in place**
to "a state of the cap" (`authSnapC`), for every reader, and the admin side's latest clause must be
guarded (the backend holds `stI` while the admin side still holds `authOwn hs`, `stI ∉ hs`). -/

/-- **A state of the cap** (candidate (i): `authSnap (.on γa)` redefined): the `i`-th of some
lower bound of the cap. Every recorded state is one (`authSnapC_of_snap`), and two at one index
agree (lower bounds are comparable, the history below them). -/
def auth.authSnapC (M : auth.AuthMode) (st : auth.AuthState) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (i : Nat) (C : List auth.AuthState), auth.capLb γa C ∗
      ⌜C[i]? = some st ∧ auth.permKeysOk st⌝)
  | M => auth.authSnap M st

/-- A recorded state is a state of the cap. -/
theorem auth.authSnapC_of_snap (stl : Loc) (R : IProp GF) (γa : auth.AuthNames)
    (st : auth.AuthState) (E' : CoPset) (hE : ↑(nroot.@"authRev") ⊆ E') :
    auth.authInv (GF := GF) stl R (.on γa) ∗ auth.authSnap (.on γa) st ={E'}=∗
      auth.authSnapC (.on γa) st := by
  simp only [auth.authSnap, auth.authSnapC]
  iintro ⟨#Hinv, ⟨%i, #Hst⟩⟩
  ihave %Hk : ⌜auth.permKeysOk st⌝ $$ [Hst]
  · iunfold auth.authStateAt at Hst; icases Hst with ⟨-, %H⟩; ipureintro; exact H
  imod auth.authStateAt_capped stl R γa i st E' hE $$ [Hinv Hst] with ⟨%C, #HC, %HCi⟩
  · iframe Hinv Hst
  imodintro
  iexists i, C
  iframe HC
  ipureintro; exact ⟨HCi, Hk⟩

/-- **The read transaction of a backend announced at `stI`** (candidate (i)): `authReadTxOk` with
`authSnapC`, the latest clause guarded: while `stI` is not in the admin side's history the state is
`stI`, after it the latest; the freshness clause at a capped index. -/
def auth.authReadTxOkC (tx : GoInterface) (R : IProp GF) (γa : auth.AuthNames)
    (stI : auth.AuthState) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗ ∃ Hs : auth.AuthState → IProp GF,
    □ ({{ R }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : auth.AuthState, Hs st ∗ auth.authSnapC (.on γa) st }}) ∗
    □ (∀ hs : List auth.AuthState,
      {{ R ∗ auth.authOwn (.on γa) hs }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : auth.AuthState, Hs st ∗ auth.authSnapC (.on γa) st ∗
          auth.authOwn (.on γa) hs ∗
          ⌜(stI ∈ hs → auth.histLast (.on γa) hs st) ∧ (stI ∉ hs → st = stI)⌝ }}) ∗
    □ (∀ i : Nat,
      {{ R ∗ auth.authPubLbM (.on γa) i }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : auth.AuthState, Hs st ∗ ∃ (j : Nat) (C : List auth.AuthState),
          auth.capLb γa C ∗ ⌜C[j]? = some st ∧ i ≤ j ∧ auth.permKeysOk st⌝ }}) ∗
    auth.authTxReads ti R Hs)

/-- The backend whose `ReadTx()` is such a transaction. (Review round 1's F1 applies here too: the
latest clause needs the write token, the freshness clause the currency, as in `authReadTxOkH`;
not repeated in this candidate, which the plan does not recommend.) -/
def auth.authBackendOkC (be : GoInterface) (R : IProp GF) (γa : auth.AuthNames)
    (stI : auth.AuthState) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (tx : GoInterface), RET #tx; auth.authReadTxOkC tx R γa stI }}))

/-- **`as.Recover(be)` with auth on, announced** (candidate (i); over `setRevision.specN`): read
**under the redefinition** `authSnap (.on γa) := authSnapC (.on γa)` (in `authInv`'s `beP`, which
holds `authBackendOk be R M`: as written here, with today's `authSnap`, `beP`'s contract at `be`
cannot be given, which is the point: candidate (i) is not statable without the redefinition).
With the whole authority at `hs` (the lock's share withdrawn from the old backend), the cap's
permission at `hs ++ N`, `stI` the last of `hs ++ N` and not in `hs` unless `N = []`: `Recover`
reads `stI` (the guarded latest clause) and appends `N` in `setRevision`. -/
abbrev auth.authStore.Recover.specC : Prop :=
  ∀ (st : Loc) (R : IProp GF) (γa : auth.AuthNames) (hs N : List auth.AuthState)
    (stI : auth.AuthState) (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.authInv st R (.on γa) ∗ auth.authOwnF (.on γa) hs ∗ auth.capAtM (.on γa) (hs ++ N) ∗
      (∃ be0 : go_etcd_io.etcd.server.v3.auth.AuthBackend,
        auth.aF go!"be" st ↦{DFrac.own (1 : Qp).half} be0) ∗
      auth.enabledHalf st (.on γa) ∗ auth.cacheHalf st (.on γa) ∗
      auth.tpAdmin st (.on γa) ∗ R ∗ ⌜be ≠ GoInterface.nil⌝ ∗ auth.authBackendOkC be R γa stI ∗
      ⌜(hs ++ N).getLast? = some stI ∧ (N ≠ [] → stI ∉ hs) ∧ auth.permsFit stI ∧
        ∀ x ∈ N, auth.permKeysOk x⌝ }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
      go!"Recover")) (Val #be))
  {{ RET #(); auth.tpAdmin st (.on γa) ∗ R ∗
      auth.aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗
      auth.authOwnF (.on γa) (hs ++ N) ∗ auth.tieRes st (.on γa) (hs ++ N) }}

end authDraft

/-! ## Q2's premise: the snapshot backend's auth contracts (trusted; one premise with boot's)

Both candidates need, besides the read contract at the new backend:
- **the store's `R`**: `beP`'s and the readers' `authRd` hold the store's read resource `R`, fixed at
  the store's construction, so the new backend's read contract is at that `R` (`authSchemaSrv`
  picks its `R` per backend): the snapshot clause is created with the boot's `R`, inside the boot
  premise, and carried to the install (TaDa: no caller-chosen `R`);
- **the lock's share of the history from the old backend**: `Recover` appends with the whole
  authority (`authOwnF`), whose batch-lock quarter is in the old backend's batch lock, which the
  install never takes (`applySnapshot` locks no auth batch transaction); so each backend's write
  token `T` gives the share back once its backend is retired (`authLockRetire`), a clause of the
  same premise;
- **`Recover`'s own read**: one `R` lent against the new backend's read token (`bkRTx`, what the
  mode-off `authRecoverOk` takes), given back after. -/

section premise
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A retired backend's write token gives the lock's share back** (persistent; trusted, with
the premise that gives `T`). The model: the lock's quarter of the history (`authLockI`) travels
**with `T`**, not in the batch lock's invariant (which the backend's commit goroutine or mvcc may
hold when `T` is retired): `T` is the apply thread's right to the backend's auth batch, held
outside a batch transaction, and `Lock()` (`authBatchTxLk`'s) moves the share from `T` into the
held lock, `Unlock()` back. So the holder of `T` can always give it up for the share, ending the
backend's write contract (and the guarded latest clause, which takes `T`). -/
def authLockRetire (γa : auth.AuthNames) (T : IProp GF) : IProp GF :=
  iprop(□ (T ==∗ ∃ st : auth.AuthState, auth.authLockI (.on γa) st))

instance authLockRetire_persistent (γa : auth.AuthNames) (T : IProp GF) :
    Persistent (authLockRetire (GF := GF) γa T) := by
  unfold authLockRetire; infer_instance

/-- The schema auth backend `abl` over the backend `be`, with the logger `lg` (read-only). -/
def ablOn (abl : Loc) (be lg : Loc) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #be : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg)

instance ablOn_persistent (abl be lg : Loc) : Persistent (ablOn (GF := GF) abl be lg) := by
  unfold ablOn; infer_instance

/-- **The write contract at every schema auth backend on `d`'s backend, at its frozen hook**
(`authSchemaSrv`'s E3l/E3n clause, at a given backend and token). -/
def authWAtHook (γa : auth.AuthNames) (d : mvcc.KBReal) (T : IProp GF) : IProp GF :=
  iprop(□ ∀ (abl' lg' : Loc) (W' Pk' : IProp GF) (f' : GoFunc),
    ablOn abl' d.be lg' -∗ backend.isBackend d.γB d.P W' Pk' d.be -∗ backend.plHookRO d.γB f' -∗
    ⌜f' ≠ func.nil⌝ -∗ auth.authWBackendOkR (authBkIface abl') (.on γa) Pk' #f' T)

instance authWAtHook_persistent (γa : auth.AuthNames) (d : mvcc.KBReal) (T : IProp GF) :
    Persistent (authWAtHook (GF := GF) γa d T) := by
  unfold authWAtHook; infer_instance

/-- **Candidate (ii): the snapshot clause** (trusted; persistent, at the store's `R`): a backend
`d` the apply thread opened, its hook frozen (`plHookRO`, the install's backend opens with the
server's hooks), its tracked auth buckets `r` holding `st` (`authBucketsAt`), `st` **recorded**
(the catch-up before `Recover`, `authCatchUpFirst`) and the lock's share at `st` (deposited, as
at boot): schema's auth backend `abl` over it meets the read contract at `R` with the history's
latest state (`authBackendOkH`), the write contract at its hook (and at every schema auth backend
on it, `authWAtHook`) for a write token `T` (with its retirement), and lends one `R` against the
backend's read token. The same statement as `authSchemaSrv` at boot, but at a recorded state
other than the boot state and the store's `R`; the read contract guarded (review round 1's F1:
the latest clause by `T`, the freshness clause by the backend's currency `Cu`, given whole).

`R`'s count (review round 1's F9): `R` is the store-level reader resource, not a token of any
backend's read lock: the store's readers hold at most `actualMaxReaders` copies (boot's premise
gives them, the threads' bound), and each backend's realization maps a held `R` to a reader slot
of its own read lock while the reader is in it. The one copy minted here is lent against the
backend's own read token `bkRTx` (the apply thread's, which `Recover`'s read then uses), so the
slots a backend needs are the store's readers' plus that one, which the token already holds: no
backend's lock needs `actualMaxReaders + 1` slots from its pool. (For the axiom check.) -/
def authSchemaSnap (γa : auth.AuthNames) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
      (r : GMap GoString backend.BktData) (st : auth.AuthState) (i : Nat),
    ⌜lg ≠ null⌝ -∗ ⌜authBucketsAt st r⌝ -∗ ablOn abl d.be lg -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
    backend.rbOwn d.γB r -∗ mvcc.bkRTx d.γB d.P d.be -∗
    auth.authStateAt γa i st -∗ auth.authLockI (.on γa) st -∗
    |==> ∃ (T : IProp GF) (Cu : Qp → IProp GF),
      auth.authBackendOkH (authBkIface abl) R γa T Cu ∗ Cu 1 ∗ auth.curFrac Cu ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) Pk #f T ∗ authWAtHook γa d T ∗
      T ∗ authLockRetire γa T ∗ R ∗ (R -∗ mvcc.bkRTx d.γB d.P d.be) ∗ backend.rbOwn d.γB r)

instance authSchemaSnap_persistent (γa : auth.AuthNames) (R : IProp GF) :
    Persistent (authSchemaSnap (GF := GF) γa R) := by
  unfold authSchemaSnap; infer_instance

/-- **Candidate (i): the snapshot clause, announced** (trusted): as `authSchemaSnap`, but `st` only
announced (the last of a lower bound of the cap), the read contract the guarded one
(`authBackendOkC`, under `authSnap`'s redefinition), and the write token completed only once the
lock's share at `st` is deposited (after `Recover`'s catch-up). -/
def authSchemaSnapC (γa : auth.AuthNames) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
      (r : GMap GoString backend.BktData) (st : auth.AuthState) (C : List auth.AuthState),
    ⌜lg ≠ null⌝ -∗ ⌜authBucketsAt st r ∧ C.getLast? = some st⌝ -∗ ablOn abl d.be lg -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
    backend.rbOwn d.γB r -∗ mvcc.bkRTx d.γB d.P d.be -∗ auth.capLb γa C -∗
    |==> ∃ T : IProp GF,
      auth.authBackendOkC (authBkIface abl) R γa st ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) Pk #f T ∗ authWAtHook γa d T ∗
      (auth.authLockI (.on γa) st ==∗ T) ∗ authLockRetire γa T ∗
      R ∗ (R -∗ mvcc.bkRTx d.γB d.P d.be) ∗ backend.rbOwn d.γB r)

instance authSchemaSnapC_persistent (γa : auth.AuthNames) (R : IProp GF) :
    Persistent (authSchemaSnapC (GF := GF) γa R) := by
  unfold authSchemaSnapC; infer_instance

/-- **The generalized premise** (Q2, one trusted premise for boot and every snapshot): today's
`authSchemaSrv`, its post also giving the boot token's retirement and the snapshot clause at the
boot's `R` (candidate (ii); candidate (i) would give `authSchemaSnapC`). What `NewServer.specM
true` would take in place of `authSchemaSrv`, and the server would carry to the install. Its boot
read contract is the guarded one (`authBackendOkH` with the boot's `T` and currency; review round
2's F3): today's `authBackendOk` is false inside a batch transaction, and after an install of
this draft its latest and freshness clauses would claim states the boot backend never received.
So boot's premise is **changed in place**, not weakened: `authSchemaSrv` does not follow from this
one (it did before the guard, `authSchemaSrv_of_G`, dropped), and its users supply the guards. -/
def authSchemaSrvG : IProp GF :=
  iprop(□ ∀ (γa : auth.AuthNames) (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
      (r : GMap GoString backend.BktData),
    ⌜lg ≠ null⌝ -∗
    ⌜(r.lookup go!"auth").getD ∅ = ∅ ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
      (r.lookup go!"authRoles").getD ∅ = ∅⌝ -∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #d.be : GoInterface) -∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.bOpen d.γB qo -∗
    backend.plHook d.γB func.nil -∗ ownToks d.γB.wb 2 -∗ backend.rbOwn d.γB r -∗
    auth.authLockI (.on γa) auth.bootState -∗
    |==> ∃ (R P : IProp GF) (f : val) (T Pre Q Post : IProp GF) (Cu : Qp → IProp GF),
      auth.authBackendOkH (authBkIface abl) R γa T Cu ∗ Cu 1 ∗ auth.curFrac Cu ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) P f T ∗
      (□ ∀ (abl' lg' : Loc) (W' Pk' : IProp GF) (f' : GoFunc),
        structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl' ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be : GoInterface) -∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl' ↦□ lg' -∗
        backend.isBackend d.γB d.P W' Pk' d.be -∗ backend.plHookRO d.γB f' -∗ ⌜f' ≠ func.nil⌝ -∗
        auth.authWBackendOkR (authBkIface abl') (.on γa) Pk' #f' T) ∗
      □ ({{ T }} (App (Val #(methods
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
          go!"CreateAuthBuckets" #abl)) (Val #())) {{ RET #(); T }}) ∗
      T ∗ mvcc.csContract P f Pre Q Post ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), R) ∗
      (Post -∗ backend.bOpen d.γB qo ∗ backend.plHook d.γB func.nil ∗
        backend.rbOwn d.γB (authBucketsAfter r)) ∗
      -- (the generalization) the boot token's retirement, the snapshot clause at the boot's `R`
      authLockRetire γa T ∗ authSchemaSnap γa R)

/-! ## The apply thread's auth resource after a jump (a finding of the glue: the fuel)

`authApplyResAt`'s fuel (`authOwnFu`: `⧗ k` with the latest revision at most `k + 1`) cannot be
kept by a jump: the image's revision counts the admin entries of the whole committed log, the
receipts only this member's applications. The draft's form takes a **base** `b` (`fuelOk hs (k +
b)`, `b < 2^61`): at boot `b = 0` (`authFuelB_of_fuel`); an install sets `b` to the image's
revision, at most `2^61` (`srvHist_wf`: at most the log's length plus one, the log below `2^61`
by raft's index bound). Today's `stepOk_of_fuel` needs `k + 1 < 2^48` at its `fuelOk` argument,
here `k + b`, which fails for a large base: the merge needs a variant at `k + b + 1 < 2^63` (the
revision's `uint64` bound and `permsFit`'s `< 2^63` both hold there; review round 2's S4). Also: the token's
retirement (`authLockRetire`), which the next install needs. In the merge both are redefinitions of
`authApplyResAt`/`authApplyResB` in place. -/

/-- The admin side's fuel at a base `b`. -/
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

/-- **The apply thread's auth resource with auth on, at the latest state `st`, on the backend `d`**
(the draft's `authApplyResAt (.on γa)`: the fuel at a base, the token's retirement, and the write
contract at every schema auth backend on `d` at its frozen hook, `authWAtHook`, from which
`authApplyResB`'s `authWBackendAt`/`isAuthStepsX` at the server's hook are built, as
`authStepsAtHook` at boot; review round 1's F4). In the merge: `authApplyResB`/`authApplyResPre`
redefined in place with these parts. -/
def authApplyResOn (γa : auth.AuthNames) (stl : Loc) (st : auth.AuthState) (d : mvcc.KBReal) :
    IProp GF :=
  iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f : val) (T : IProp GF) (be : GoInterface)
      (b : Nat), auth.authOwn (.on γa) hs ∗ authFuelB hs b ∗ auth.tieRes stl (.on γa) hs ∗
    auth.authWBackendOk be (.on γa) P f T ∗ T ∗ authLockRetire γa T ∗ authWAtHook γa d T ∗
    auth.tpAdmin stl (.on γa) ∗ ⌜hs.getLast? = some st⌝)

/-! ## `Recover` at the install, with auth on (the server-level triple, and its glue) -/

/-- **`ast.Recover(NewAuthBackend(lg, newbe))` at the install, auth on** (candidate (ii); the
mode-on twin of `authRecoverOk`): the apply thread's auth resource at the applied log `A`'s state
`sa`, the store's tie to the log (`authHistTie`), the image's committed log `A'` extending `A`
(`srvRLogLb`), the new backend `dn` opened with its hook frozen, its tracked auth buckets `r`
holding `A'`'s state, and the snapshot clause at the store's `R`: after `Recover`, the store on
the new backend (`authBeOn`) and the apply thread's auth resource at `A'`'s state, on the new
backend's write contract and its hook clause (`authWAtHook` at `dn`); the backend resources back. -/
abbrev authRecoverOn.spec : Prop :=
  ∀ (ast abl lg : Loc) (dO dn : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
    (r : GMap GoString backend.BktData) (γa : auth.AuthNames) (R : IProp GF) (E : apply.AEnv GF)
    (γr : ReadNames) (A A' : List EntryModel) (sa : auth.AuthState),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      authBeOn ast dO.be ∗ authApplyResOn γa ast sa dO ∗
      auth.authInv ast R (.on γa) ∗ authSchemaSnap γa R ∗
      authHistTie E γr srvAuthSt0 ∗ srvRLogLb γr.raft A' ∗
      ⌜A <+: A' ∧ sa = srvAuthAtLog γr.kv srvAuthSt0 A ∧ A'.length < 2 ^ 61⌝ ∗
      ⌜lg ≠ null⌝ ∗ ablOn abl dn.be lg ∗
      backend.isBackend dn.γB dn.P W Pk dn.be ∗ backend.plHookRO dn.γB f ∗ ⌜f ≠ func.nil⌝ ∗
      backend.rbOwn dn.γB r ∗ mvcc.bkRTx dn.γB dn.P dn.be ∗
      ⌜authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A') r⌝ }}
    (App (Val (ast @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
      go!"Recover")) (Val #(authBkIface abl)))
  {{ RET #(); authBeOn ast dn.be ∗ authApplyResOn γa ast (srvAuthAtLog γr.kv srvAuthSt0 A') dn ∗
      backend.rbOwn dn.γB r ∗ mvcc.bkRTx dn.γB dn.P dn.be }}

end premise

section glue
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The glue: `Recover` at the install from `Recover.specP`** (candidate (ii)): the tie's
catch-up half (`authHistTie_catchup`) and the list (`catchup_list`), the old token retired for the
lock's share (`authLockRetire`), the history caught up before the call (`authCatchUpFirst`), the
snapshot clause at the new backend (`authSchemaSnap`), then `Recover.specP`; the fuel moved to the
image's base. -/
theorem authRecoverOn_glue (hRec : auth.authStore.Recover.specP (GF := GF) (hG := hG)) :
    authRecoverOn.spec (GF := GF) (hG := hG) := by
  intro ast abl lg dO dn W Pk f r γa R E γr A A' sa hM
  iintro %Φ ⟨#Hpkg, Hbeon, Hres, #Hinv, #Hsnap, #Htie, #HA', %Hp, %Hlg, #Habl, #HisB, #Hhk,
    %Hf, Hrb, Hrt, %Hbk⟩ HΦ
  obtain ⟨hpre, hsa, hlen⟩ := Hp
  obtain ⟨hk, hfit, hsmall, hrev⟩ := srvHist_wf γr.kv A' hlen
  iunfold authApplyResOn at Hres
  icases Hres with ⟨%hs, %P0, %f0, %T, %be, %b, Hown, Hfu, Htr, -, HT, #Hret, -, Htp, %Hlast⟩
  -- the tie's half: the history a prefix of the image's, the cap at it
  imod authHistTie_catchup E γr γa A A' hs ⊤ hM hpre (by rw [Hlast, hsa]; rfl) (by simp) (by simp)
    $$ [Hown] with ⟨Hown, %Hpfx, #Hcap⟩
  · simp only [srvAuthSt0] at *; iframe Htie HA' Hown
  obtain ⟨hcat, hcl⟩ := catchup_list γr.kv A' hs Hpfx
  -- the old backend's token retired: the lock's share, joined with the admin side's
  ihave #Hret0 := Hret
  iunfold authLockRetire at Hret0
  imod Hret0 $$ HT with ⟨%st0, Hlk⟩
  ihave ⟨HoF, -⟩ := auth.authOwn_lockI_join (.on γa) hs st0 $$ Hown Hlk
  ihave #Hcap' : auth.capLb γa (hs ++ (srvHist γr.kv A').drop hs.length) $$ [Hcap]
  · rw [hcat]; iexact Hcap
  -- the history caught up before the call
  imod auth.authCatchUpFirst ast R γa hs ((srvHist γr.kv A').drop hs.length)
      (srvAuthAtLog γr.kv srvAuthSt0 A') ⊤ (by simp)
      (fun x hx => hk x (List.mem_of_mem_drop hx)) hcl $$ [Hinv HoF Hcap']
    with ⟨HoP, Hlk, #HstI⟩
  · iframe Hinv HoF Hcap'
  -- the snapshot clause at the new backend
  ihave #Hsn := Hsnap
  iunfold authSchemaSnap at Hsn
  imod Hsn $$ %lg %abl %dn %W %Pk %f %r %(srvAuthAtLog γr.kv srvAuthSt0 A')
      %((hs ++ (srvHist γr.kv A').drop hs.length).length - 1) [] [] Habl HisB Hhk [] Hrb Hrt HstI Hlk
    with ⟨%T', %Cu, #HokH, HCu, #HCf, #HwR, #HwH, HT', #Hret', HR, HRb, Hrb⟩
  · ipureintro; exact Hlg
  · ipureintro; exact Hbk
  · ipureintro; exact Hf
  -- `Recover.specP`
  iunfold authBeOn at Hbeon
  icases Hbeon with ⟨%abl0, %lg0, -, Hbe, -, -⟩
  iunfold auth.tieRes at Htr
  icases Htr with ⟨%b0, %sc, Hfl, #Hev, Hca, #Hsc, -⟩
  ihave Hen := auth.flagAt_enabledHalf ast (.on γa) b0 $$ [Hfl]
  · iframe Hfl Hev
  ihave Hch := auth.cacheHalf_of_at ast (.on γa) sc $$ Hca Hsc
  wp_apply (hRec ast R γa hs ((srvHist γr.kv A').drop hs.length) (srvAuthAtLog γr.kv srvAuthSt0 A')
      (authBkIface abl) T' Cu) $$ [Hbe Hen Hch Htp HR HoP HT' HCu]
    as ⟨Htp, HR, HT', Hbe, Hown, Htr⟩
  · iframe Hinv HoP Hen Hch Htp HR HokH HstI HT' HCu HCf
    isplitl [Hbe]
    · iexists authBkIface abl0; iexact Hbe
    ipureintro
    exact ⟨by simp [authBkIface], hcl, hfit⟩
  ihave Hrt := HRb $$ HR
  iapply HΦ
  iframe Hrb Hrt
  isplitl [Hbe]
  · iunfold authBeOn; iexists abl, lg
    iunfold ablOn at Habl
    icases Habl with ⟨#H1, #H2⟩
    iframe Hbe H1 H2; ipureintro; exact Hlg
  iunfold authApplyResOn
  ihave #Hw := auth.authWBackendOk_of_R (authBkIface abl) (.on γa) Pk #f T' $$ HwR
  iexists hs ++ (srvHist γr.kv A').drop hs.length, Pk, #f, T', authBkIface abl,
    (srvAuthAtLog γr.kv srvAuthSt0 A').revision
  iframe Hown Htr Hw HT' Hret' HwH Htp
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

/-- **The server's auth store with its snapshot clause** (persistent; auth on): the store its
`authStore` field holds, its invariant at its read resource `Ra` (at the install, the apply
environment's `E.RD`, the resource the admin steps at the new hook use), and `authSchemaSnap` at
`Ra`.
What `NewServer.specM true` would give from the generalized premise (`authSchemaSrvG`) and `run`
carry to each install (as `bootOk`'s `#HmetaSnap`). -/
def srvAuthSnapOk (s : Loc) (γa : auth.AuthNames) (Ra : IProp GF) : IProp GF :=
  iprop(∃ ast : Loc, srvAuthStoreAddr s ↦□ auth.authIface ast ∗ auth.authInv ast Ra (.on γa) ∗
    authSchemaSnap γa Ra)

instance srvAuthSnapOk_persistent (s : Loc) (γa : auth.AuthNames) (Ra : IProp GF) :
    Persistent (srvAuthSnapOk (GF := GF) s γa Ra) := by
  unfold srvAuthSnapOk; infer_instance

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
`authApplyResB (.on γa)`, is the draft's `authApplyResOn` form (the fuel at a base, the token's
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
       auth.authInv ast E.RD (.on γa) ∗ authSchemaSnap γa E.RD ∗ srvRLogLb γr.raft A' ∗
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

/-- **`run`'s auth-on snapshot-payload job** (`EtcdServer__run.lean` ~:1413, statement only; the
auth-on twin of J8b's mode-off job): from the loop's resources at `A` (`applyResOn`) and the
payload's (`rnApplyTok_recv`'s snapshot branch, at a fresh start), with the store's snapshot clause
(`srvAuthSnapOk`, which `isServerRunOn` does not carry today: a finding, the line `run` needs from
`NewServer`), `applyAll.specSnapOn` gives the loop's resources at the image's log `A'`. Besides
what J8b's mode-off job takes of `isServerRun` (`γr.kv.log0 = [[], []]`, `#HmetaSnap`'s premise,
`|boot| ≤ i`), the mode-on start's chain (`γr.kv.ch0 = alarmChain true false false`) and the
snapshot directory's image in the mode (`srvSnapRO`'s `snapDirInv … (srvImage …)` is the mode-off
certificate: `srvImageOn`, #7-on). -/
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
