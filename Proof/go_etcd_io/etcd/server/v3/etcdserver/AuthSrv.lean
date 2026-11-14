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
  backend). The simple provider's contract takes its index waiter's (auth-schema-fix S1 option A,
  decided by etcd-grove-81, 2026-11-12: until then the false hypothesis `auth.ValidSpec`): the caller
  passes a waiter returning a channel `auth.anyRecv` once the auth names' readiness cell is shot
  (`auth.tpShot γy`, `γa.rdy = γy`), which `NewServer` proves of its closure over `s.applyWait`
  (`srvTpInv`) and `start` fires; the request side holds once ready (`auth.tpReady`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSnapKit
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
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Close

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

-- `authOpenQ`, `authBkts`, `ablOn`, `authWAtHook`, `authRdSlots`, `authRdSupply`, `authSchemaSnap`:
-- `AuthSnapKit.lean`'s (below `SnapRO`, which carries the snapshot clause).

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

**Write-back** (auth-schema-fix F1, decided by etcd-grove-81, 2026-11-12): the realization owns no
backend write-back tokens and makes none; each write spends the server's (`Wb := backend.wbTok d.γB`,
paid from the apply loop's receipts and, at boot, `NewServer`'s): a batch `Unlock` two (schema's
`authBatchTx.Unlock` is the backend batch's `Unlock` then `Commit`), `ForceCommit` one,
`CreateAuthBuckets` one, `GetAllRoles` two (a batch). Until F1 the premise handed it a bag of two
tokens (`ownToks d.γB.wb 2`) for every batch it would ever commit.
**The lend** (`authBkLend`, F2): a read-only observation of the auth buckets (an abstract `RL` with a
law against the batch lock's `rbOwn`), with no write authority; until F2 it lent the buckets'
`rbPart`, through which a client could write them.
**The write contract's text** (`auth.authBatchTxLkR`): `GetAllRoles` lists only `auth.roleListed`
names (F3: Go's range `[0x00, 0xff)`); `UnsafePutUser` takes valid UTF-8 roles (F4: a proto3
`string`); both puts take a non-empty name of a message without unknown fields (the axiom
re-review's m1 and M1, 2026-11-13).

Refutations fixed against earlier texts: S0's four (`notes/auth-schema-srv-refuted.md`, F1-F4, the
four above); before them, five: (1) the latest clause took `T`; (2) the published index's authority
was shared with the realization, publication needed `T`; (3) no `rbOwn` of the auth buckets came
back; (4) `Cu`/`T` stood for an open share the realization keeps until both are surrendered; (5) `T`
and `Cu` were functions of `γc`, which `beP` and the apply thread share. Review rounds A1/A2: the
auth buckets taken idle (no pending write: the readers see `r`); the succession right taken (one
live backend). -/
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
    backend.plHook d.γB func.nil -∗ backend.rbOwnIn d.γB authBkts r -∗
    auth.authSucc γa -∗
    auth.authLockI (.on γa) auth.bootState -∗ auth.authPubQ γa (1 : Qp).half 0 -∗
    |={⊤}=> ∃ (R P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) (γc : auth.AuthBkNames),
      auth.authBackendOk (authBkIface abl) R (.on γa) γc ∗ auth.authCur γc 1 ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) P f (auth.authWTok γc) (backend.wbTok d.γB) ∗
      authWAtHook γa d γc ∗ authBkLend γa γc d ∗
      □ ({{ auth.authWTok γc ∗ backend.wbTok d.γB }} (App (Val #(methods
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
          go!"CreateAuthBuckets" #abl)) (Val #())) {{ RET #(); auth.authWTok γc }}) ∗
      auth.authWTok γc ∗ auth.authPubTok γa ∗
      auth.authBkLife γa γc (backend.bOpen d.γB authOpenQ) ∗
      srvApi.csContractA P f Pre Q Post ∗
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
  | .on _ => iprop(backend.bOpen d.γB authOpenQ ∗ authRdSlots d ∗ backend.wbTok d.γB ∗
      backend.wbTok d.γB)
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

-- `authSnapKitM`: `AuthSnapKit.lean`'s.

/-- **The realization's share of the backend's open token, in the mode `M`** (R-D1, 2026-11-04):
`authOpenQ` in `on γa` (what `authKitIn` gave the store's construction), nothing otherwise. -/
def authOpenM (M : auth.AuthMode) (d : mvcc.KBReal) : IProp GF :=
  match M with
  | .on _ => backend.bOpen d.γB authOpenQ
  | _ => iprop(True)

/-- **`NewServer`'s abandoned auth store** (R-D1, 2026-11-04; `notes/decisions.md`, "R-D1: the
one-shot Close"): `NewServer`'s error after `NewAuthStore` (the transport's start) drops the store;
with every reader's resource (`authRdSupply RD`) and the apply thread's resources
(`authApplyResPre`, at any state), the realization's share of the backend's open token back
(`authOpenM`), for the backend's `Close`. In `on γa` (R-D2, 2026-11-04; `notes/decisions.md`, "R-D2:
the auth store's currency in an invariant") of the store's currency in its invariant
(`auth.authRd_abandon`: every reader's ticket, so no reader in), the backend retired and released;
trivially otherwise. -/
def authAbandonM (M : auth.AuthMode) (stl : Loc) (d : mvcc.KBReal) (RD : IProp GF) : IProp GF :=
  iprop(□ ∀ st : auth.AuthState, authRdSupply RD -∗ authApplyResPre M stl st d RD ={⊤}=∗
    authOpenM M d)

instance authAbandonM_persistent (M : auth.AuthMode) (stl : Loc) (d : mvcc.KBReal) (RD : IProp GF) :
    Persistent (authAbandonM (GF := GF) M stl d RD) := by
  unfold authAbandonM; infer_instance

/-- **The apply thread's share and the realization's make the constructors' half** (R-D1): with
`authKitIn_take`'s `srvOpenQ M`, `authOpenM M d` is the half `authKitIn_take` split. -/
theorem authOpenM_join (M : auth.AuthMode) (d : mvcc.KBReal) :
    backend.bOpen (GF := GF) d.γB (srvOpenQ M) ∗ authOpenM M d ⊢ backend.bOpen d.γB (1 : Qp).half := by
  cases M with
  | on γa =>
    simp only [authOpenM, srvOpenQ, authOpenQ]
    iintro ⟨Ho1, Ho2⟩
    ihave Ho := (backend.bOpen_add (GF := GF) d.γB (1 : Qp).half.half (1 : Qp).half.half).2
      $$ [Ho1 Ho2]
    · iframe Ho1 Ho2
    rw [Qp.half_add_half]
    iexact Ho
  | _ =>
    simp only [authOpenM, srvOpenQ]
    iintro ⟨Ho, -⟩
    iexact Ho

/-- **The auth store's construction in the mode `M`** with the token provider `tp` (see the file
header): `NewAuthStore`'s axiom's triple, the apply contract in the mode `M`, at a resource `K`
the kit holds (`True` in the mode `off`; the admin side's authority, the batch lock's half and the
provider's admin resource in the mode `on`). -/
def authStoreKit (M : auth.AuthMode) (tp : GoInterface) : IProp GF :=
  iprop(∃ K : IProp GF, K ∗ □ ∀ (lg : Loc) (ab : GoInterface) (abl : Loc)
      (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (r : GMap GoString backend.BktData) (cost : w64),
    {{ K ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ zapLoggerOk lg ∗
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
        -- (auth-schema-fix S1 option A) the request side once the token provider is ready (`start`
        -- fires `auth.tpReady`)
        □ (auth.tpReady M -∗ isReqAuth st RD) ∗
        authApplyOkM M stl RD ∗ authStoreLatestM M st RD stl ∗ authStoreLbM M st RD ∗
        authPublishM M stl ∗
        -- (E3zb) with auth on, the request side bound to the request context's token
        □ (⌜M.isOn = true⌝ → auth.tpReady M -∗ isReqAuthBound st RD M) ∗
        authApplyResPre M stl (auth.bump auth.bootState) d RD ∗ authCapM M stl ∗
        -- (R-D1, 2026-11-04) the store abandoned on `NewServer`'s error path
        authAbandonM M stl d RD ∗
        -- (D22 J1a, 2026-10-26) in the mode `off`, the store's `Recover` on a new backend
        -- (`NewAuthStore`'s axiom's `authRecoverOk`)
        □ (⌜M = auth.AuthMode.off⌝ → authRecoverOk stl) ∗
        -- (R2b-3d stage 5b, 2026-11-05) in the mode `off`, the store's `Close` (`NewAuthStore`'s
        -- axiom's `authCloseOk`), for `Cleanup`
        □ (⌜M = auth.AuthMode.off⌝ → authCloseOk stl) ∗
        -- (the auth-on snapshot plan's decision 8) in the mode `on`, its snapshot clause
        authSnapKitM M stl RD ∗
        -- (authkv's Main, 2026-10-30) with auth on, the store's cost field, read-only
        -- (`BcryptCost()`'s; `newAuthStore_on`'s); (C1's A4, 2026-10-31) and its `Authenticate`
        -- side (`authnStoreOk`, of its invariant: `authnStoreOk_of_authInv`)
        □ (⌜M.isOn = true⌝ →
          (∃ c : w64, structFieldRef go_etcd_io.etcd.server.v3.auth.authStore go!"bcryptCost" stl ↦□ c) ∗
          authnStoreOk st RD) }})

/-- **`NewTokenProvider` at the server, with auth on or off** (see the file header): with auth on
(`on = true`) its options `"simple"`, its TTL positive and the index waiter `iw` returning, once the
readiness cell `γy` is shot (`auth.tpShot γy`: the server has started; auth-schema-fix S1 option A,
decided by etcd-grove-81, 2026-11-12), a channel a receive completes on (`auth.anyRecv`); with no
error, a mode `M` with `M.isOn = on` (with auth on, `.on γa` for some auth names: the auth plan's
E3zb, 2026-10-28; their readiness cell `γy`) and the auth store's construction in it. -/
abbrev authSrvTP (on : Bool) : Prop :=
  ∀ (lg : Loc) (opts : GoString) (iw : GoFunc) (ttl : time.Duration) (γy : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ zapLoggerOk lg ∗
      ⌜on = true → opts = go!"simple" ∧ 0 < sint.Z ttl⌝ ∗
      □ (⌜on = true⌝ → ∀ idx : w64,
        {{ auth.tpShot γy }} (App (Val #iw) (Val #idx)) {{ (ch : Loc), RET #ch; auth.anyRecv ch }}) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewTokenProvider)) (Val #lg))
      (Val #opts)) (Val #iw)) (Val #ttl))
  {{ (tp err : GoInterface), RET (PairV #tp #err);
      ⌜err = GoInterface.nil → tp ≠ GoInterface.nil⌝ ∗
      (⌜err = GoInterface.nil⌝ -∗ |==> ∃ M : auth.AuthMode,
        ⌜M.isOn = on ∧ (on = true → ∃ γa, M = .on γa) ∧
          (∀ γa : auth.AuthNames, M = .on γa → γa.rdy = γy)⌝ ∗ authStoreKit M tp) }}


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

/-- **A closer of the store at the token provider's admin share** (R2b-3d stage 5b, 2026-11-05),
of `authStore.Close`'s proof under the store's invariant: what `Cleanup` would take with auth on
(the admin share the apply thread's, `authApplyRes`). -/
theorem authCloser_of_inv (hAC : auth.authStore.Close.spec (GF := GF) (hG := hG)) (stl : Loc)
    (R : IProp GF) (M : auth.AuthMode) :
    auth.authInv stl R M ⊢ authCloser stl (auth.tpAdmin stl M) := by
  iintro #Hinv
  iunfold authCloser
  iintro !> %Φ !> ⟨#Hpkg, Ht⟩ HΦ
  iapply (hAC stl R M) $$ [Ht]
  · iframe Hpkg Hinv Ht
  iexact HΦ

/-- **The kit in the mode `off`**, of `NewAuthStore`'s axiom. -/
theorem authStoreKit_off (h30 : auth.NewAuthStore.spec (GF := GF) (hG := hG)) (tp : GoInterface) :
    ⊢ authStoreKit (GF := GF) .off tp := by
  iunfold authStoreKit
  iexists iprop(True)
  isplitr
  · itrivial
  iintro !> %lg %ab %abl %d %W %Pk %qo %r %cost %Φ !> ⟨-, #Hpkg, #Hlg, %Htp, %Hfit, %Hab, #Habbe,
    #Hablg, #HB, Ho, Hh, Hwb, Hrb, -, %Hr, %Hhas⟩ HΦ
  -- (the auth-on snapshot plan's Prove step) the axiom at the auth buckets, idle
  ihave Hrb := backend.rbOwnIn_part _ _ _ $$ Hrb
  iapply (h30 lg ab tp cost abl d W Pk qo authBkts r (fun _ h => h) Hhas.1 Hhas.2.1
    Hhas.2.2) $$ [Ho Hh Hwb Hrb]
  · iframe Hpkg Habbe Hablg HB Ho Hh Hwb Hrb
    isplitr
    · iapply zapLoggerOk_orNil; iexact Hlg
    ipureintro; exact ⟨Htp, Hfit, Hab, Or.inl Hr.1, Hr.2⟩
  iintro !> %st ⟨Ho, Hh, Hr, %RD, %stl, %Hst, Hbe, Hsl, #Hreq, #Hok, #HauR, #HauC⟩
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
  iframe Hbe Hsl
  isplitr
  · ipureintro; exact Hst
  isplitr
  · iintro !> -; iexact Hreq
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
  · iunfold authAbandonM
    iintro !> %_st _ _
    unfold authOpenM
    imodintro; itrivial
  isplitr
  · iintro !> -
    iexact HauR
  isplitr
  · iintro !> -
    iexact HauC
  isplitr
  · unfold authSnapKitM; itrivial
  iintro !> %h; exact absurd h (by decide)

/-- **`authSrvTP false`**, of `NewTokenProvider`'s proof and `NewAuthStore`'s axiom. -/
theorem authSrvTP_off (h25 : auth.NewTokenProvider.spec (GF := GF) (hG := hG))
    (h30 : auth.NewAuthStore.spec (GF := GF) (hG := hG)) :
    authSrvTP (GF := GF) false := by
  intro lg opts iw ttl γy
  iintro %Φ ⟨#Hpkg, #Hlg, -, -⟩ HΦ
  iapply (h25 lg opts iw ttl) $$ [Hpkg]
  · iframe Hpkg; iapply zapLoggerOk_orNil; iexact Hlg
  iintro !> %tp %err ⟨%Htp, -⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Htp
  iintro -
  imodintro
  iexists .off
  isplitr
  · ipureintro; exact ⟨rfl, fun h => absurd h (by decide), fun _ h => by cases h⟩
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
    HpubQ⟩, #Hpkg, #Hlg, %Htp, %Hfit, %Hab, #Habbe, #Hablg, #HB, Hopen, Hhook, Hwb, Hrbo, HkIn, %Hr,
    %Hhas⟩ HΦ
  simp only [authKitIn]
  icases HkIn with ⟨HopQ, Hslots0, Hwb3, Hwb4⟩
  -- (auth-schema-fix F1) the boot's four write-back tokens: the kit's two and `authKitIn`'s two
  icases ownToks_add_1 1 1 d.γB.wb $$ Hwb with ⟨Hwb1, Hwb2⟩
  ihave Hwb1 : backend.wbTok d.γB $$ [Hwb1]
  · iunfold backend.wbTok; iexact Hwb1
  ihave Hwb2 : backend.wbTok d.γB $$ [Hwb2]
  · iunfold backend.wbTok; iexact Hwb2
  ihave #HD := hD22
  -- (E2k) the fuel at the history the store starts at (`[bootState, bump bootState]`)
  ihave Hfu := auth.authFuel_boot (GF := GF)
  imod Hfu
  iunfold authSchemaSrv at HD
  ihave HD' := HD $$ %γa %lg %abl %d %W %Pk %qo %r [] [] [] [] HB Hopen HopQ Hslots0 Hhook Hrbo
    Hsucc HI HpubQ
  · iapply zapLoggerOk_ne_null; iexact Hlg
  · ipureintro; exact Hr
  · iunfold ablOn; iframe Habbe Hablg
  · ipureintro; exact Hhas
  imod HD' with ⟨%R, %P, %f, %Pre, %Q, %Post, %γc, #Hrdok, Hcu, #HwokR, #HwAt, #HLend, #HCreate, HT, Hpt,
    #Hlife, Hcs, HRs, Hback, #Hsnap⟩
  -- (the Prove step) the current backend's names, set to the new backend's: the store's half and
  -- the apply thread's
  imod (ghostVar_update γc γa.bk γ0) $$ Hbk with Hbk
  icases (ghostVar_split_half γa.bk 1 γc).1 $$ Hbk with ⟨Hbk, Hbk'⟩
  subst Hab
  -- (R-D2, 2026-11-04) the store hands out `authRdN - 1` readers, each with its ticket for the
  -- store's currency, and no more (`auth.authRdTotal`)
  have hR : backend.authRdN - 1 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; unfold backend.authRdN; decide
  wp_apply (auth.newAuthStore_on h_Warn h_Int h_Revision h_commit h_metrics h_refresh lg
      (authBkIface abl) tp cost
      (interface.mk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
        #abl) γa γc R P f (auth.authWTok γc) (backend.wbTok d.γB) A Pre Q Post [auth.bootState] auth.bootState rfl
      auth.bootState_permsFit ⟨auth.bootState, List.mem_singleton_self _, rfl⟩
      (backend.authRdN - 1) hR)
    $$ [$Hpkg $Hrdok Hbk $Hcu $HwokR $HCreate $HT $Hwb1 $Hwb2 $Hwb3 $Hwb4 $Hcs $HtpA $HA $Hown $Hcur $Hcn]
    as %st ⟨%stp, %hs', %Hst, #Hinv, HWR, HtpAd, HPost, Hown', %Hhs', #Hbc, #Htot, Hslots⟩
  · iframe; isplitr
    · iexact Hlg
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
    isplitr
    · iunfold authStepsAtHook
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
        hRoleGrantPermissionB hAuthnB stp R (.on γa) Pk' f' (auth.authWTok γc) (backend.wbTok d.γB)
        (beOn d.be)
        $$ [$Hpkg $Hinv]
    -- (P6.2) what an install needs: the lifecycle at the backend's open share, the hook clause,
    -- the admin steps at any backend
    iunfold authInstallPre
    iframe Hlife HwAt HLend
    iunfold authStepsAny
    iintro !> %bel %Pk' %f' %T' %Wb'
    iunfold adminW
    iapply apply.isAuthStepsX_of_authInvTB hEnableB hUserAddB hRoleAddB hUserGrantRoleB
      hRoleGrantPermissionB hAuthnB stp R (.on γa) Pk' f' T' Wb' (beOn bel)
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
    iapply zapLoggerOk_ne_null; iexact Hlg
  isplitl [Hslots HRs]
  · icases replicate_takeN _ (backend.authRdN - 1) _ (by omega) $$ HRs with ⟨HRs, -⟩
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
  -- (R-D2, 2026-11-04) the abandoned store: every reader's ticket, the apply thread's write side and
  -- its backend's lifecycle at the realization's share
  isplitr
  · iunfold authAbandonM
    iintro !> %st HRDs HAR
    unfold authRdSupply authOpenM
    simp only [authApplyResPre]
    icases HAR with ⟨%hs0, %P0, %f00, %T, %be0, -, -, -, HW, -, Hpt, -, -, -, -, HIP⟩
    iunfold authInstallPre at HIP
    icases HIP with ⟨#Hlife, -⟩
    iapply (auth.authRd_abandon stp R γa (backend.authRdN - 1) T) $$ Htot HRDs HW Hpt Hlife
  -- (D22 J1a) the mode is `on`: no `Recover` clause
  isplitr
  · iintro !> %Hm
    exfalso; cases Hm
  -- nor a `Close` clause (R2b-3d stage 5b)
  isplitr
  · iintro !> %Hm
    exfalso; cases Hm
  -- (decision 8) the snapshot clause: the invariant and `authSchemaSrv`'s clause, at `R`
  isplitr
  · unfold authSnapKitM
    iexists R
    iframe Hinv Hsnap
    ipureintro; rfl
  iintro !> -
  iframe Hbc
  iapply authnStoreOk_of_authInv hCP hGT h_Revision stp R (.on γa) $$ [$Hpkg $Hinv]

/-- **`authSrvTP true`** (see the file header): the simple provider, its names the auth names'
token names, the auth names allocated over the boot state, the kit in the mode `on`. -/
theorem authSrvTP_on (h25 : auth.NewTokenProvider.spec (GF := GF) (hG := hG))
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
  intro lg opts iw ttl γy
  iintro %Φ ⟨#Hpkg, #Hlg, %Hon, #Hiw⟩ HΦ
  obtain ⟨hopts, httl⟩ := Hon rfl
  iapply (h25 lg opts iw ttl) $$ [Hpkg]
  · iframe Hpkg; iapply zapLoggerOk_orNil; iexact Hlg
  iintro !> %tp %err ⟨%Htp, Hres⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Htp
  iintro %Herr
  icases Hres with (%Hno | ⟨%p, %γt, %γf, %Hp, #Hiwf, #Hok, HA, Hfr⟩)
  · exfalso; rcases Hno with h | h
    · exact h hopts
    · omega
  obtain ⟨-, rfl⟩ := Hp
  imod (auth.authBoot_alloc (GF := GF) γt γf γy) with ⟨%γa, %Hγ, Hown, Hcur, HI, Hcap, #Hcn, Hbk,
    Hsucc, HpubQ⟩
  obtain ⟨hγt, hγf, hγy⟩ := Hγ
  subst hγt hγf hγy
  -- (auth-schema-fix S1 option A) the provider's index waiter: the caller's waiter, once ready
  ihave #Hwok : auth.simpleWaitOk p γa.rdy $$ []
  · iunfold auth.simpleWaitOk
    iexists iw
    iframe Hiwf
    iintro !> %idx
    ihave #Ht := Hiw $$ []
    · ipureintro; rfl
    ihave #Ht2 := Ht $$ %idx
    iexact Ht2
  ihave #HtpA := auth.tokenSimple_okA_run h_Debug h_String h_GTP p γa $$ [$Hpkg $Hok $Hwok]
  imodintro
  iexists (.on γa)
  isplitr
  · ipureintro
    exact ⟨rfl, fun _ => ⟨γa, rfl⟩, fun γa' h => by cases h; rfl⟩
  iapply (authStoreKit_on h_Warn h_Int h_Revision h_commit h_metrics h_refresh hCtx hTLS hPut hRange
    hDel hAdmin hEn hPutL hRangeL hDelL hAdminL hRangeLb hEnLb hRevLb hAdminLb hPutLb hEnableB hUserAddB hRoleAddB hUserGrantRoleB
    hRoleGrantPermissionB hAuthnB hCP hGT hD22 _ γa (auth.simpleAdmin p))
    $$ [$HtpA $HA $Hown $Hcur $HI $Hfr $Hcap $Hcn Hsucc $Hbk $HpubQ]
  unfold auth.authSucc; iexact Hsucc

/-! ### The kit's resources at `NewServer` (the Prove step's P5), by the mode -/

/-- **The buckets the constructing thread holds idle after the store's construction, by the
mode**: in `on γa` all but the auth ones (which the realization keeps), in the others all. -/
def kitSet (M : auth.AuthMode) (n : GoString) : Prop :=
  match M with
  | .on _ => ¬ authBkts n
  | _ => True

theorem kitSet_of (M : auth.AuthMode) (n : GoString) (h : ¬ authBkts n) : kitSet M n := by
  cases M <;> simp only [kitSet] <;> first | trivial | exact h

/-- **The kit's pre from the constructors' half of the open token, the auth share of the
reader slots and two write-back tokens**: in `on` a quarter of the token, the slots and the tokens
(auth-schema-fix F1: the boot's two beyond the kit's) to the kit, the apply thread keeping
`srvOpenQ` (a quarter); in the others the half kept, the slots and the tokens dropped. -/
theorem authKitIn_take (M : auth.AuthMode) (d : mvcc.KBReal) :
    backend.bOpen (GF := GF) d.γB (1 : Qp).half ∗ authRdSlots d ∗ backend.wbTok d.γB ∗
        backend.wbTok d.γB ⊢
      authKitIn M d ∗ backend.bOpen d.γB (srvOpenQ M) := by
  cases M with
  | on γa =>
    simp only [authKitIn, srvOpenQ, authOpenQ]
    iintro ⟨Ho, Hs, Hw1, Hw2⟩
    icases (backend.bOpen_add (GF := GF) d.γB (1 : Qp).half.half (1 : Qp).half.half).1 $$ [Ho]
      with ⟨Ho1, Ho2⟩
    · rw [Qp.half_add_half]; iexact Ho
    iframe Ho1 Hs Ho2 Hw1 Hw2
  | _ =>
    simp only [authKitIn, srvOpenQ]
    iintro ⟨Ho, -⟩
    iframe Ho

/-- **The idle buckets after the store's construction, by the mode**: the other buckets the
constructing thread kept, with what the kit gives back (`authKitOut`), at the buckets after
`NewAuthStore` (`authBucketsAfter`, which changes only the auth ones). -/
theorem authKitOut_join (M : auth.AuthMode) (d : mvcc.KBReal) (r : GMap GoString backend.BktData) :
    backend.rbOwnIn (GF := GF) d.γB (fun n => ¬ authBkts n) r ∗ authKitOut M d r ⊢
      backend.rbOwnIn d.γB (kitSet M) (authBucketsAfter r) := by
  have hag : ∀ n, ¬ authBkts n → r.lookup n = (authBucketsAfter r).lookup n := by
    intro n hn
    simp only [authBkts, auth.authBkts, not_or] at hn
    simp [authBucketsAfter]
    rw [if_neg (Ne.symm hn.2.2), if_neg (Ne.symm hn.2.1), if_neg (Ne.symm hn.1)]
  iintro ⟨Hn, Hk⟩
  ihave Hn := (backend.rbOwnIn_congr (GF := GF) d.γB _ r (authBucketsAfter r) hag).1 $$ Hn
  cases M with
  | on γa =>
    iapply (backend.rbOwnIn_set (GF := GF) d.γB (fun n => ¬ authBkts n) (kitSet (.on γa)) _
      (fun n => Iff.rfl)).1
    iexact Hn
  | off =>
    simp only [authKitOut]
    ihave H := (backend.rbOwnIn_split_compl (GF := GF) d.γB authBkts _).2 $$ [Hk Hn]
    · iframe Hk Hn
    iapply (backend.rbOwnIn_set (GF := GF) d.γB (fun _ => True) (kitSet .off) _
      (fun n => Iff.rfl)).1
    iexact H
  | any =>
    simp only [authKitOut]
    ihave H := (backend.rbOwnIn_split_compl (GF := GF) d.γB authBkts _).2 $$ [Hk Hn]
    · iframe Hk Hn
    iapply (backend.rbOwnIn_set (GF := GF) d.γB (fun _ => True) (kitSet .any) _
      (fun n => Iff.rfl)).1
    iexact H

/-- **The idle buckets after the constructors, as the rest resource holds them**: the cluster's
idle, the others of the mode's rest set (`restSet`) a part. -/
theorem rbOwnIn_kit_rest (M : auth.AuthMode) (γB : backend.BNames) (r : GMap GoString backend.BktData) :
    backend.rbOwnIn (GF := GF) γB (kitSet M) r ⊢
      backend.rbOwnIn γB membership.clusterBkts r ∗ backend.rbPart γB (restSet M) r := by
  have hcl : ∀ n, membership.clusterBkts n → ¬ authBkts n := by
    intro n hc ha
    simp only [membership.clusterBkts, membership.memberBkts] at hc
    simp only [authBkts, auth.authBkts] at ha
    rcases hc with (h | h) | h <;> rcases ha with h' | h' | h' <;> rw [h] at h' <;> exact absurd h' (by decide)
  have hset : ∀ n, kitSet M n ↔ (membership.clusterBkts n ∨ restSet M n) := by
    intro n
    cases M <;> simp only [kitSet, restSet]
    all_goals first
      | exact ⟨fun _ => Classical.em _ |>.elim Or.inl Or.inr, fun _ => trivial⟩
      | exact ⟨fun h => (Classical.em (membership.clusterBkts n)).elim Or.inl
          (fun hc => Or.inr ⟨hc, h⟩), fun h => h.elim (hcl n) And.right⟩
  iintro H
  ihave H := (backend.rbOwnIn_set (GF := GF) γB _ _ r hset).1 $$ H
  icases (backend.rbOwnIn_split (GF := GF) γB _ _ r (fun n h1 h2 => restSet_ncl M n h2 h1)).1 $$ H
    with ⟨Hc, Hr⟩
  iframe Hc
  iapply backend.rbOwnIn_part $$ Hr

end proof

end EtcdGrove
end Perennial
