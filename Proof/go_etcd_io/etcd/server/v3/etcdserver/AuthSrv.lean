/-
**The server's auth store in either auth mode** (the auth plan's E2i, 2026-10-26;
`notes/decisions.md`, "E2i of the auth plan"). Lean-first (no Rocq counterpart).

`NewServer` calls `auth.NewTokenProvider` and, after `mvcc.New` (whose watchable store's owner tag
names the auth mode, `auth.modeTag`), `auth.NewAuthStore`. Its proof (`NewServer.wp_proofM`) takes
the two through one contract, `authSrvTP on`, generic in whether auth is on: the token provider's
call gives, with no error, a mode `M` (`M.isOn = on`) and the auth store's construction in that
mode (`authStoreKit M tp`): `NewAuthStore`'s axiom's triple with the apply contract in the mode
`M` (`authApplyOkM`), at a resource `K` the kit holds.

* **auth off** (`authSrvTP_off`): from `NewTokenProvider`'s proof and `NewAuthStore`'s axiom, the
  mode `off` (`NewServer.spec`'s, the closed theorems').
* **auth on** (`authSrvTP_on`): the simple provider (`"simple"`, a positive TTL); the auth names
  allocated over the boot state with the provider's token names (`auth.authBoot_alloc`), the store
  from its proof in the mode `on γa` (`auth.newAuthStore_on`), its request side and apply contract
  of its invariant (`authSrvContracts_on`). What only D22 can prove is the named premise
  `authSchemaSrv`: given the batch lock's half of the history at the boot state, schema's auth
  backend over the server's backend meets the store's backend contracts (`authBackendOk`,
  `authWBackendOkR`, `CreateAuthBuckets`), taking the backend resources `NewAuthStore`'s axiom
  takes and giving back what it gives back (as `auth.authSchemaBoot`, E2e, at the server's
  backend). The simple provider's contract rests on `isValidSimpleToken`'s spec for any context
  (`auth.ValidSpec`, a premise: it is proved on contexts only, `tokenSimple_okCtx`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthApplyOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthApplyRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StoreLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthReqDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot
public import Proof.go_etcd_io.etcd.server.v3.auth.TokenKeeperRun
public import Spec.go_etcd_io.etcd.server.v3.auth.NewAuthStore
public import Spec.go_etcd_io.etcd.server.v3.auth.NewTokenProvider

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The rest buckets after `NewAuthStore` on the buckets `r` (its buckets created, the revision
`1` committed: `NewAuthStore`'s axiom's post). -/
abbrev authBucketsAfter (r : GMap GoString backend.BktData) : GMap GoString backend.BktData :=
  ((r.insert go!"auth" authBoot).insert go!"authUsers" ∅).insert go!"authRoles" ∅

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
def authRdSupply (RD : IProp GF) : IProp GF :=
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
def authSchemaSrv : IProp GF :=
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

instance authSchemaSrv_persistent : Persistent (authSchemaSrv (GF := GF)) := by
  unfold authSchemaSrv; infer_instance

/-- **What the store's construction takes beside the backend, in the mode `M`** (the auth-on
snapshot plan's Prove step, 2026-11-03; `authSchemaSrv`'s): in `on γa`, the realization's open share
`authOpenQ` and the store's share of the backend's reader slots (`authRdSlots`); nothing otherwise. -/
def authKitIn (M : auth.AuthMode) (d : mvcc.KBReal) : IProp GF :=
  match M with
  | .on _ => iprop(backend.bOpen d.γB authOpenQ ∗ authRdSlots d)
  | _ => iprop(True)

/-- **What the store's construction gives back of the auth buckets, in the mode `M`** (the Prove
step): in `on γa` nothing (their write authority stays with the realization, `authSchemaSrv`); in
the other modes the client's idle part of them after `NewAuthStore` (its axiom's). -/
def authKitOut (M : auth.AuthMode) (d : mvcc.KBReal) (r : GMap GoString backend.BktData) :
    IProp GF :=
  match M with
  | .on _ => iprop(True)
  | _ => backend.rbOwnIn d.γB authBkts (authBucketsAfter r)

/-- **The cap of the auth store's history, at the start, in the mode `M`** (H5, 2026-10-29): in
`on γa`, the cap's authority at the start's history `[bootState, bump bootState]`, with the store's
invariant (which keeps the history below the cap, `auth.authStateAt_capped`), for the server to put
in its tie of the history to the log (`authHistTie`); `True` in the other modes. -/
def authCapM (M : auth.AuthMode) (stl : Loc) : IProp GF :=
  match M with
  | .on γa => iprop(auth.capAuth γa [auth.bootState, auth.bump auth.bootState] ∗
      ∃ R : IProp GF, auth.authInv stl R (.on γa))
  | _ => iprop(True)

/-- **The auth store's construction in the mode `M`** with the token provider `tp` (see the file
header): `NewAuthStore`'s axiom's triple, the apply contract in the mode `M`, at a resource `K`
the kit holds (`True` in the mode `off`; the admin side's authority, the batch lock's half and the
provider's admin resource in the mode `on`). -/
def authStoreKit (M : auth.AuthMode) (tp : GoInterface) : IProp GF :=
  iprop(∃ K : IProp GF, K ∗ □ ∀ (lg : Loc) (ab : GoInterface) (abl : Loc)
      (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (r : GMap GoString backend.BktData) (cost : w64),
    {{ K ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ ∗
        ⌜tp ≠ GoInterface.nil⌝ ∗ ⌜authRecordsFit⌝ ∗ ⌜ab = authBkIface abl⌝ ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be : GoInterface) ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg ∗
        backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗
        backend.plHook d.γB func.nil ∗ ownToks d.γB.wb 2 ∗ backend.rbOwnIn d.γB authBkts r ∗
        authKitIn M d ∗
        ⌜(r.lookup go!"auth").getD ∅ = ∅ ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
          (r.lookup go!"authRoles").getD ∅ = ∅⌝ ∗
        -- (2026-11-02, the backend-auth-split stage) the auth buckets in the backend's table, as
        -- `NewAuthStore`'s axiom now takes them
        ⌜d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI⌝ }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg))
        (Val #ab)) (Val #tp)) (Val #cost))
    {{ (st : GoInterface), RET #st; backend.bOpen d.γB qo ∗ backend.plHook d.γB func.nil ∗
        authKitOut M d r ∗
        ∃ (RD : IProp GF) (stl : Loc), ⌜st = auth.authIface stl⌝ ∗ authBeOn stl d.be ∗
        authRdSupply RD ∗
        isReqAuth st RD ∗ authApplyOkM M stl RD ∗ authStoreLatestM M st RD stl ∗ authStoreLbM M st RD ∗
        authPublishM M stl ∗
        -- (E3zb) with auth on, the request side bound to the request context's token
        □ (⌜M.isOn = true⌝ → isReqAuthBound st RD M) ∗
        authApplyResPre M stl (auth.bump auth.bootState) d RD ∗ authCapM M stl ∗
        -- (D22 J1a, 2026-10-26) in the mode `off`, the store's `Recover` on a new backend
        -- (`NewAuthStore`'s axiom's `authRecoverOk`)
        □ (⌜M = auth.AuthMode.off⌝ → authRecoverOk stl) ∗
        -- (authkv's Main, 2026-10-30) with auth on, the store's cost field, read-only
        -- (`BcryptCost()`'s; `newAuthStore_on`'s); (C1's A4, 2026-10-31) and its `Authenticate`
        -- side (`authnStoreOk`, of its invariant: `authnStoreOk_of_authInv`)
        □ (⌜M.isOn = true⌝ →
          (∃ c : w64, structFieldRef go_etcd_io.etcd.server.v3.auth.authStore go!"bcryptCost" stl ↦□ c) ∗
          authnStoreOk st RD) }})

/-- **`NewTokenProvider` at the server, with auth on or off** (see the file header): with auth on
(`on = true`) its options `"simple"` and its TTL positive; with no error, a mode `M` with
`M.isOn = on` (with auth on, `.on γa` for some auth names: the auth plan's E3zb, 2026-10-28) and the
auth store's construction in it. -/
abbrev authSrvTP (on : Bool) : Prop :=
  ∀ (lg : Loc) (opts : GoString) (iw : GoFunc) (ttl : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ ∗
      ⌜on = true → opts = go!"simple" ∧ 0 < sint.Z ttl⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewTokenProvider)) (Val #lg))
      (Val #opts)) (Val #iw)) (Val #ttl))
  {{ (tp err : GoInterface), RET (PairV #tp #err);
      ⌜err = GoInterface.nil → tp ≠ GoInterface.nil⌝ ∗
      (⌜err = GoInterface.nil⌝ -∗ |==> ∃ M : auth.AuthMode,
        ⌜M.isOn = on ∧ (on = true → ∃ γa, M = .on γa)⌝ ∗ authStoreKit M tp) }}


/-- **The server's auth store's cost field** (persistent; authkv's Main, 2026-10-30): the server's
`authStore` field is a `*authStore` whose `bcryptCost` field is read-only, what `BcryptCost()`
returns (`bcryptCostOk`, the Auth service's `UserAdd`). `NewServer.specM true`'s. -/
def srvBcryptField (s : Loc) : IProp GF :=
  iprop(∃ (stl : Loc) (c : w64), structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"authStore" s ↦□ auth.authIface stl ∗
    structFieldRef go_etcd_io.etcd.server.v3.auth.authStore go!"bcryptCost" stl ↦□ c)

instance srvBcryptField_persistent (s : Loc) : Persistent (srvBcryptField (GF := GF) s) := by
  unfold srvBcryptField; infer_instance

/-- **The server's auth store with auth on** (persistent; C1's A4, 2026-10-31): `srvBcryptField`'s
cost field, and the store's `Authenticate` side at the server's reader resource `RD`
(`authnStoreOk`: `CheckPassword`, `GenTokenPrefix`, `Revision`, what `EtcdServer.Authenticate`
calls). `NewServer.specM true`'s. -/
def srvAuthStoreOn (s : Loc) (RD : IProp GF) : IProp GF :=
  iprop(∃ (stl : Loc) (c : w64),
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"authStore" s ↦□ auth.authIface stl ∗
    structFieldRef go_etcd_io.etcd.server.v3.auth.authStore go!"bcryptCost" stl ↦□ c ∗
    authnStoreOk (auth.authIface stl) RD)

instance srvAuthStoreOn_persistent (s : Loc) (RD : IProp GF) :
    Persistent (srvAuthStoreOn (GF := GF) s RD) := by
  unfold srvAuthStoreOn; infer_instance

theorem srvBcryptField_of_authStoreOn (s : Loc) (RD : IProp GF) :
    srvAuthStoreOn (GF := GF) s RD ⊢ srvBcryptField s := by
  iintro H
  iunfold srvAuthStoreOn at H
  icases H with ⟨%stl, %c, #Hf, #Hc, -⟩
  iunfold srvBcryptField
  iexists stl, c
  iframe Hf Hc

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **The kit in the mode `off`**, of `NewAuthStore`'s axiom. -/
theorem authStoreKit_off (h30 : auth.NewAuthStore.spec (GF := GF) (hG := hG)) (tp : GoInterface) :
    ⊢ authStoreKit (GF := GF) .off tp := by
  iunfold authStoreKit
  iexists iprop(True)
  isplitr
  · itrivial
  iintro !> %lg %ab %abl %d %W %Pk %qo %r %cost %Φ !> ⟨-, #Hpkg, %Hlg, %Htp, %Hfit, %Hab, #Habbe,
    #Hablg, #HB, Ho, Hh, Hwb, Hrb, -, %Hr, %Hhas⟩ HΦ
  -- (the auth-on snapshot plan's Prove step) the axiom at the auth buckets, idle
  ihave Hrb := backend.rbOwnIn_part _ _ _ $$ Hrb
  iapply (h30 lg ab tp cost abl d W Pk qo authBkts r (fun _ h => h) Hhas.1 Hhas.2.1
    Hhas.2.2) $$ [Ho Hh Hwb Hrb]
  · iframe Hpkg Habbe Hablg HB Ho Hh Hwb Hrb
    ipureintro; exact ⟨Hlg, Htp, Hfit, Hab, Hr⟩
  iintro !> %st ⟨Ho, Hh, Hr, %RD, %stl, %Hst, Hbe, Hsl, #Hreq, #Hok, #HauR⟩
  iapply HΦ
  iframe Ho Hh
  isplitl [Hr]
  · simp only [authKitOut]; iexact Hr
  have hR : backend.authRdN - 1 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; unfold backend.authRdN; decide
  icases replicate_takeN _ (backend.authRdN - 1) _ hR $$ Hsl with ⟨Hsl, -⟩
  ihave Hsl : authRdSupply RD $$ [Hsl]
  · unfold authRdSupply; iexact Hsl
  iexists RD, stl
  iframe Hbe Hsl Hreq
  isplitr
  · ipureintro; exact Hst
  isplitr
  · iExactEq Hok; rfl
  isplitr
  · unfold authStoreLatestM; itrivial
  isplitr
  · unfold authStoreLbM; itrivial
  isplitr
  · unfold authPublishM; itrivial
  isplitr
  · iintro !> %h; exact absurd h (by decide)
  isplitr
  · unfold authApplyResPre
    itrivial
  isplitr
  · unfold authCapM; itrivial
  isplitr
  · iintro !> -
    iexact HauR
  iintro !> %h; exact absurd h (by decide)

/-- **`authSrvTP false`**, of `NewTokenProvider`'s proof and `NewAuthStore`'s axiom. -/
theorem authSrvTP_off (h25 : auth.NewTokenProvider.spec (GF := GF) (hG := hG))
    (h30 : auth.NewAuthStore.spec (GF := GF) (hG := hG)) :
    authSrvTP (GF := GF) false := by
  intro lg opts iw ttl
  iintro %Φ ⟨#Hpkg, %Hlg, -⟩ HΦ
  iapply (h25 lg opts iw ttl) $$ [Hpkg]
  · iframe Hpkg; ipureintro; exact Hlg
  iintro !> %tp %err ⟨%Htp, -⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Htp
  iintro -
  imodintro
  iexists .off
  isplitr
  · ipureintro; exact ⟨rfl, fun h => absurd h (by decide)⟩
  iapply (authStoreKit_off h30 tp)

set_option maxRecDepth 16384 in
/-- **The kit in the mode `on γa`** (see the file header): the store's proof in the mode `on γa`
at the boot state, over D22's named premise, with the admin side's authority, the batch lock's
half and the other half of the latest state's variable at the boot state, the provider's
contract with its admin resource `A`, and the token rights' empty authority (C1's A1). -/
theorem authStoreKit_on
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_commit : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_metrics : auth.authStore.setupMetricsReporter.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG))
    (hPut : auth.authStore.IsPutPermitted.spec (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.spec (GF := GF) (hG := hG))
    (hDel : auth.authStore.IsDeleteRangePermitted.spec (GF := GF) (hG := hG))
    (hAdmin : auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG))
    (hEn : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (hPutL : auth.authStore.IsPutPermitted.specL (GF := GF) (hG := hG))
    (hRangeL : auth.authStore.IsRangePermitted.specL (GF := GF) (hG := hG))
    (hDelL : auth.authStore.IsDeleteRangePermitted.specL (GF := GF) (hG := hG))
    (hAdminL : auth.authStore.IsAdminPermitted.specL (GF := GF) (hG := hG))
    (hRangeLb : auth.authStore.IsRangePermitted.specLb (GF := GF) (hG := hG))
    (hEnLb : auth.authStore.IsAuthEnabled.specLb (GF := GF))
    (hRevLb : auth.authStore.Revision.specLb (GF := GF))
    (hAdminLb : auth.authStore.IsAdminPermitted.specLb (GF := GF) (hG := hG))
    (hPutLb : auth.authStore.IsPutPermitted.specLb (GF := GF) (hG := hG))
    (hEnableB : auth.authStore.AuthEnable.specTB (GF := GF) (hG := hG))
    (hUserAddB : auth.authStore.UserAdd.specTSureB (GF := GF) (hG := hG))
    (hRoleAddB : auth.authStore.RoleAdd.specTB (GF := GF) (hG := hG))
    (hUserGrantRoleB : auth.authStore.UserGrantRole.specTB (GF := GF) (hG := hG))
    (hRoleGrantPermissionB : auth.authStore.RoleGrantPermission.specTB (GF := GF) (hG := hG))
    (hAuthnB : auth.authStore.Authenticate.specTB (GF := GF) (hG := hG))
    (hCP : auth.authStore.CheckPassword.spec (GF := GF) (hG := hG))
    (hGT : auth.authStore.GenTokenPrefix.spec (GF := GF) (hG := hG))
    (hD22 : ⊢ authSchemaSrv (GF := GF))
    (tp : GoInterface) (γa : auth.AuthNames) (A : IProp GF) :
    auth.tokenProviderOkA tp (.on γa) A ∗ A ∗ auth.authOwn (.on γa) [auth.bootState] ∗
      auth.authStoreInit γa [auth.bootState] auth.bootState ∗ auth.authLockI (.on γa) auth.bootState ∗
      ghostMapAuth γa.fresh 1 (∅ : GMap GoString Unit) ∗
      auth.capAuth γa [auth.bootState, auth.bump auth.bootState] ∗
      auth.capNext (.on γa) [auth.bootState] (auth.bump auth.bootState) ∗
      auth.authSucc γa ∗ (∃ γ0 : auth.AuthBkNames, ghostVar γa.bk 1 γ0) ∗
      auth.authPubQ γa (1 : Qp).half 0 ⊢
      authStoreKit (GF := GF) (.on γa) tp := by
  iintro ⟨#HtpA, HA, Hown, Hcur, HI, Hfr, Hcap, #Hcn, Hsucc, ⟨%γ0, Hbk⟩, HpubQ⟩
  iunfold authStoreKit
  iexists iprop(A ∗ auth.authOwn (.on γa) [auth.bootState] ∗
    auth.authStoreInit γa [auth.bootState] auth.bootState ∗
    auth.authLockI (.on γa) auth.bootState ∗ ghostMapAuth γa.fresh 1 (∅ : GMap GoString Unit) ∗
    auth.capAuth γa [auth.bootState, auth.bump auth.bootState] ∗
    auth.authSucc γa ∗ ghostVar γa.bk 1 γ0 ∗ auth.authPubQ γa (1 : Qp).half 0)
  iframe HA Hown Hcur HI Hfr Hcap Hsucc Hbk HpubQ
  iintro !> %lg %ab %abl %d %W %Pk %qo %r %cost %Φ !> ⟨⟨HA, Hown, Hcur, HI, Hfr, Hcap, Hsucc, Hbk,
    HpubQ⟩, #Hpkg, %Hlg, %Htp, %Hfit, %Hab, #Habbe, #Hablg, #HB, Hopen, Hhook, Hwb, Hrbo, HkIn, %Hr,
    %Hhas⟩ HΦ
  simp only [authKitIn]
  icases HkIn with ⟨HopQ, Hslots0⟩
  ihave #HD := hD22
  -- (E2k) the fuel at the history the store starts at (`[bootState, bump bootState]`)
  ihave Hfu := auth.authFuel_boot (GF := GF)
  imod Hfu
  iunfold authSchemaSrv at HD
  ihave HD' := HD $$ %γa %lg %abl %d %W %Pk %qo %r [] [] [] [] HB Hopen HopQ Hslots0 Hhook Hwb Hrbo
    Hsucc HI HpubQ
  · ipureintro; exact Hlg
  · ipureintro; exact Hr
  · iunfold ablOn; iframe Habbe Hablg
  · ipureintro; exact Hhas
  imod HD' with ⟨%R, %P, %f, %Pre, %Q, %Post, %γc, #Hrdok, Hcu, #HwokR, #HwAt, #HCreate, HT, Hpt,
    #Hlife, Hcs, HRs, Hback, #Hsnap⟩
  -- (the Prove step) the current backend's names, set to the new backend's: the store's half and
  -- the apply thread's
  imod (ghostVar_update γc γa.bk γ0) $$ Hbk with Hbk
  icases (ghostVar_split_half γa.bk 1 γc).1 $$ Hbk with ⟨Hbk, Hbk'⟩
  subst Hab
  wp_apply (auth.newAuthStore_on h_Warn h_Int h_Revision h_commit h_metrics h_refresh lg
      (authBkIface abl) tp cost
      (interface.mk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
        #abl) γa γc R P f (auth.authWTok γc) A Pre Q Post [auth.bootState] auth.bootState rfl
      auth.bootState_permsFit ⟨auth.bootState, List.mem_singleton_self _, rfl⟩)
    $$ [$Hpkg $Hrdok Hbk $Hcu $HwokR $HCreate $HT $Hcs $HtpA $HA $Hown $Hcur $Hcn]
    as %st ⟨%stp, %hs', %Hst, #Hinv, HWR, HtpAd, HPost, Hown', %Hhs', #Hbc, Hslots⟩
  · iframe; isplitr
    · ipureintro; exact Hlg
    isplitr
    · ipureintro; rfl
    unfold auth.authBkCur; iexact Hbk
  ihave ⟨Hopen, Hhook⟩ := Hback $$ HPost
  iunfold auth.authWRAt at HWR
  icases HWR with ⟨⟨Hbe, #Hwok⟩, HT', Hen, Hca⟩
  -- (E2k) the boot state's revision is `0`: the history `[bootState, bump bootState]`, its fuel
  have hhs' : hs' = [auth.bootState, auth.bump auth.bootState] := by
    rcases Hhs' with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd rfl h
    · exact h
  ihave ⟨#HisReq, #HisAuth⟩ := authSrvContracts_on hCtx hTLS hPut hRange hDel hAdmin hEn h_Revision
    stp R γa $$ [$Hpkg $Hinv]
  -- (E3l) the store's checks at the latest state, of its invariant
  ihave #HstL : authStoreLatestM (.on γa) (auth.authIface stp) (auth.authRd stp R (.on γa)) stp
    $$ []
  · simp only [authStoreLatestM]
    iintro !> %γc'
    iapply apply.isAuthStoreL_of_authInv hPutL hRangeL hDelL hAdminL stp R (.on γa) γc'
      $$ [$Hpkg $Hinv]
  -- (E3s) the range check at a reader's lower bound, of its invariant
  ihave #HstLb : authStoreLbM (.on γa) (auth.authIface stp) (auth.authRd stp R (.on γa)) $$ []
  · unfold authStoreLbM
    iintro !> %n #Hlb
    isplitr
    · iapply apply.isAuthStoreRangeLb_of_authInv hRangeLb stp R (.on γa) n $$ [$Hpkg $Hinv $Hlb]
    -- (the lease-src plan) the lease checks' methods at the same lower bound
    · iapply isAuthStoreLeaseLb_of_authInv hEnLb hRevLb hAdminLb hPutLb hRangeLb stp R (.on γa) n
        $$ [$Hpkg $Hinv $Hlb]
  -- (E3t) publication, of its invariant
  ihave #HstPub := authPublishM_of_authInv stp R γa $$ Hinv
  -- (E3zb) the request side bound to the request context's token, of its invariant
  ihave #HbB := isReqAuthBound_of_authInv hCtx stp R (.on γa) $$ [$Hpkg $Hinv]
  subst hhs'
  -- (E2v) the halves tied to the start's history, whose states are disabled
  ihave ⟨Hown', HX⟩ := auth.tieRes_of_disabled stp γa [auth.bootState, auth.bump auth.bootState]
    (by intro s hs; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hs
        rcases hs with rfl | rfl <;> rfl)
    (by intro s hs s' hs'; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hs hs'
        rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> rfl) $$ [Hown' Hen Hca]
  · iframe Hown' Hen Hca
  -- (E3l) the store's admin steps, keeping its backend, at the server's admin resource; (E3n) at
  -- whichever post-lock hook the server freezes
  ihave HAR : authApplyResPre (.on γa) stp (auth.bump auth.bootState) d (auth.authRd stp R (.on γa)) $$ [Hown' Hfu HT' Hbk' Hpt HX HtpAd Hfr]
  · unfold authApplyResPre
    iexists [auth.bootState, auth.bump auth.bootState], P, f, γc, (authBkIface abl)
    iunfold auth.authOwnFu
    iframe Hown' Hfu HX HtpAd Hwok Hfr Hpt
    isplitl [HT' Hbk']
    · iunfold auth.authWHeld; iframe HT'; unfold auth.authBkCur; iexact Hbk'
    isplitr
    · iexists (backend.bOpen d.γB authOpenQ); iexact Hlife
    isplitr
    · ipureintro; rfl
    iunfold authStepsAtHook
    iintro !> %W' %Pk' %f' #HB' #Hhk' %Hf'
    isplitr
    · iunfold authWBackendAt
      iintro !> %abl' %lg' #Hb #Hl
      iapply auth.authWBackendOk_of_R
      iunfold authWAtHook at HwAt
      iapply HwAt $$ %abl' %lg' %W' %Pk' %f' [] HB' Hhk' []
      · iunfold ablOn; iframe Hb Hl
      ipureintro; exact Hf'
    iunfold adminW
    iapply apply.isAuthStepsX_of_authInvTB hEnableB hUserAddB hRoleAddB hUserGrantRoleB
      hRoleGrantPermissionB hAuthnB stp R (.on γa) Pk' #f' (auth.authWTok γc) (beOn d.be)
      $$ [$Hpkg $Hinv]
  iapply HΦ
  iframe Hopen Hhook
  isplitr
  · simp only [authKitOut]; itrivial
  iexists (auth.authRd stp R (.on γa)), stp
  subst Hst
  iframe HisReq HisAuth HstL HstLb HstPub HAR
  isplitr
  · ipureintro; rfl
  isplitl [Hbe]
  · iunfold authBeOn
    iexists abl, lg
    iframe Hbe Habbe Hablg
    ipureintro; exact Hlg
  isplitl [Hslots HRs]
  · have hR : backend.authRdN - 1 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
      rw [sync.rwmutex.actualMaxReaders_unseal]; unfold backend.authRdN; decide
    icases replicate_takeN _ (backend.authRdN - 1) _ hR $$ Hslots with ⟨Hslots, -⟩
    icases replicate_takeN _ (backend.authRdN - 1) _ (by omega) $$ HRs with ⟨HRs, -⟩
    ihave Hsl := BigSepL.bigSepL_sep_eqv.2 $$ [Hslots HRs]
    · iframe Hslots HRs
    unfold authRdSupply
    iapply (replicate_mono _ (auth.authRd stp R (.on γa)) _
      (by iintro ⟨⟨He, Hc, Hb⟩, HR⟩; unfold auth.authRd; iframe He Hc Hb HR)) $$ Hsl
  isplitr
  · iintro !> -; iexact HbB
  isplitl [Hcap]
  · unfold authCapM
    isplitl [Hcap]
    · iexact Hcap
    iexists R; iexact Hinv
  -- (D22 J1a) the mode is `on`: no `Recover` clause
  isplitr
  · iintro !> %Hm
    exfalso; cases Hm
  iintro !> -
  iframe Hbc
  iapply authnStoreOk_of_authInv hCP hGT h_Revision stp R (.on γa) $$ [$Hpkg $Hinv]

/-- **`authSrvTP true`** (see the file header): the simple provider, its names the auth names'
token names, the auth names allocated over the boot state, the kit in the mode `on`. -/
theorem authSrvTP_on (h25 : auth.NewTokenProvider.spec (GF := GF) (hG := hG))
    (hValid : auth.ValidSpec (GF := GF) (hG := hG))
    (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_GTP : auth.tokenSimple.genTokenPrefix.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_commit : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_metrics : auth.authStore.setupMetricsReporter.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG))
    (hPut : auth.authStore.IsPutPermitted.spec (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.spec (GF := GF) (hG := hG))
    (hDel : auth.authStore.IsDeleteRangePermitted.spec (GF := GF) (hG := hG))
    (hAdmin : auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG))
    (hEn : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (hPutL : auth.authStore.IsPutPermitted.specL (GF := GF) (hG := hG))
    (hRangeL : auth.authStore.IsRangePermitted.specL (GF := GF) (hG := hG))
    (hDelL : auth.authStore.IsDeleteRangePermitted.specL (GF := GF) (hG := hG))
    (hAdminL : auth.authStore.IsAdminPermitted.specL (GF := GF) (hG := hG))
    (hRangeLb : auth.authStore.IsRangePermitted.specLb (GF := GF) (hG := hG))
    (hEnLb : auth.authStore.IsAuthEnabled.specLb (GF := GF))
    (hRevLb : auth.authStore.Revision.specLb (GF := GF))
    (hAdminLb : auth.authStore.IsAdminPermitted.specLb (GF := GF) (hG := hG))
    (hPutLb : auth.authStore.IsPutPermitted.specLb (GF := GF) (hG := hG))
    (hEnableB : auth.authStore.AuthEnable.specTB (GF := GF) (hG := hG))
    (hUserAddB : auth.authStore.UserAdd.specTSureB (GF := GF) (hG := hG))
    (hRoleAddB : auth.authStore.RoleAdd.specTB (GF := GF) (hG := hG))
    (hUserGrantRoleB : auth.authStore.UserGrantRole.specTB (GF := GF) (hG := hG))
    (hRoleGrantPermissionB : auth.authStore.RoleGrantPermission.specTB (GF := GF) (hG := hG))
    (hAuthnB : auth.authStore.Authenticate.specTB (GF := GF) (hG := hG))
    (hCP : auth.authStore.CheckPassword.spec (GF := GF) (hG := hG))
    (hGT : auth.authStore.GenTokenPrefix.spec (GF := GF) (hG := hG))
    (hD22 : ⊢ authSchemaSrv (GF := GF)) :
    authSrvTP (GF := GF) true := by
  intro lg opts iw ttl
  iintro %Φ ⟨#Hpkg, %Hlg, %Hon⟩ HΦ
  obtain ⟨hopts, httl⟩ := Hon rfl
  iapply (h25 lg opts iw ttl) $$ [Hpkg]
  · iframe Hpkg; ipureintro; exact Hlg
  iintro !> %tp %err ⟨%Htp, Hres⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Htp
  iintro %Herr
  icases Hres with (%Hno | ⟨%p, %γt, %γf, %Hp, -, #Hok, HA, Hfr⟩)
  · exfalso; rcases Hno with h | h
    · exact h hopts
    · omega
  obtain ⟨-, rfl⟩ := Hp
  imod (auth.authBoot_alloc (GF := GF) γt γf) with ⟨%γa, %Hγ, Hown, Hcur, HI, Hcap, #Hcn, Hbk,
    Hsucc, HpubQ⟩
  obtain ⟨hγt, hγf⟩ := Hγ
  subst hγt hγf
  ihave #HtpA := auth.tokenSimple_okA_run hValid h_Debug h_String h_GTP p γa $$ [$Hpkg $Hok]
  imodintro
  iexists (.on γa)
  isplitr
  · ipureintro; exact ⟨rfl, fun _ => ⟨γa, rfl⟩⟩
  iapply (authStoreKit_on h_Warn h_Int h_Revision h_commit h_metrics h_refresh hCtx hTLS hPut hRange
    hDel hAdmin hEn hPutL hRangeL hDelL hAdminL hRangeLb hEnLb hRevLb hAdminLb hPutLb hEnableB hUserAddB hRoleAddB hUserGrantRoleB
    hRoleGrantPermissionB hAuthnB hCP hGT hD22 _ γa (auth.simpleAdmin p))
    $$ [$HtpA $HA $Hown $Hcur $HI $Hfr $Hcap $Hcn Hsucc $Hbk $HpubQ]
  unfold auth.authSucc; iexact Hsucc

end proof

end EtcdGrove
end Perennial
