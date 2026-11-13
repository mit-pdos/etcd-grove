/-
The authentication example's results (`examples/etcd/auth/authkv.go`; the auth plan's E2b), restated,
with the trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq
counterpart).

* **`authkv_Main`** (`Link.lean`'s `etcd_auth.wp_Main`): `Main()` -- one member with the simple token
  provider, auth set up and enabled, four principals' workloads inside and outside `[a, b)`, and
  checks that panic if the server let a principal do what the auth state does not permit -- does
  not panic and returns `Ok`, `Failed` or `WatchEnded` (`Spec/.../auth/Main.lean`). `Main.wp_proof`
  is proved (2026-10-31), and since 2026-11-13 no `sorry` is reached
  (`etc/tcb-collections/authkv.txt`).
* **`authkv_Permitted`** (`Link.lean`'s `etcd_auth.wp_Permitted`): the program's verdict
  `Permitted(who, k)` is `permittedK who k`; and **`authkv_granted_iff`** (`Model.lean`'s
  `granted_setupSt_iff`): that is the model's verdict at the set-up's state for the workload's
  users, so the program's checks are stated in the model's terms.
* **`authkv_badToken`** (`ClientAuth.lean`'s `simpleTok_ne_badToken`): the bad principal's token
  is not one the simple provider makes; **`authkv_badToken_not_issued`** (`tokIssued_badToken`,
  the auth plan's E2c): it was issued to no one, every issued token having the simple provider's
  shape; **`authkv_token_one_user`** (`auth.tokIssued_agree`, E2c): a token is issued to one user.
* The checks `Main` makes (the auth plan's E2f): **`authkv_CheckHistory`** (the history's check
  returns when every event after the set-up is a write its key's principal was permitted,
  `histOk`, the principal the key names, `writerK`), **`authkv_checkKVs`** and
  **`authkv_checkTxnReads`** (a reply's check returns when its keys are the principal's to read);
  **`authkv_reqCtx`** (a request's context: the bad principal's carries `badtoken` appended to its
  outgoing metadata, over the trust-boundary spec of grpc's `AppendToOutgoingContext`, contract
  C3); and **`authkv_bad_unbound`** (`ClientAuth.lean`'s `badCtx_unbound`): a handler context
  delivering such metadata (C2, C4) gives no auth info in the mode `on γa`.
* **`authkv_startServer`** (the auth plan's E3zb; linked here, not in `Link.lean`, which links
  only `.spec`s): `startServer` starts the member with auth on (`memberUpOn`), from
  `server_new_auth_on` (its named premise: D22's `authSchemaSrv`; until auth-schema-fix S1 also
  the false `auth.ValidSpec`) and
  `server_Start` at the auth slot's `on γa`.
* **`authkv_SetUp`** (`Link.lean`'s `etcd_auth.wp_SetUp`; E2h, the auth-mode merge's 5b): `SetUp`,
  through a client with no user, at etcd's Auth specs, from the client's view of the auth history:
  on success the history frozen at a log whose auth state is `setupSt r`, published.
* **`etcd_auth_safe`** (`Adequacy.lean`'s `etcd_auth_adequate`; the `etcd_auth_safe` Scope's S2,
  2026-11-13): the closed theorem. Every real execution of `n` steps of `authkv`'s initialization
  followed by `Main()`, from a fresh state with one thread, has no stuck thread, no thread ended in
  a panic (so none of `Main`'s checks failed), and the main thread's result, if any, is `0`, `1`
  or `2`; under watchkv's hypotheses at authkv's configuration and D22's `authSchemaSrv` (a named
  hypothesis, trusted text: `Adequacy.lean`'s header).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.startServer
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Results

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]

/-- **The member started with auth on** (`startServer.lean`; E3zb): `NewServer.specM true`
(`server_new_auth_on`, with its named premises) and `Start.spec` (`server_Start`) at the auth slot's
`on γa`. (The auth component's stage 3, 2026-11-04: until then `Start.specOn`, `server_Start_on`,
which also took `ErrorStringLeaf`.) -/
theorem authkv_startServer (hD22 : ⊢ authSchemaSrv (GF := GF)) :
    etcd_auth.startServer.spec (GF := GF) (hG := hG) :=
  etcd_auth.startServer.wp_proof etcdstart.features.wp_NewDefaultServerFeatureGate
    (server_new_auth_on hD22) server_Start

/-- **`Main` does not panic** (`Link.lean`'s `etcd_auth.wp_Main`). At the
hypothesis on the semantics every client-building `Main` has (`DialWithBalancerBody`, through
`newUserClient`'s `clientv3.New`; watchkv's, cachekv's, ...), and the member's start with auth on
(`authkv_startServer`, 2026-10-30: `Link.lean` links only `.spec`s): its named premises
(D22's `authSchemaSrv`; auth-schema-fix S1, 2026-11-12: no longer the false `auth.ValidSpec`) and
hypotheses on the
semantics (`ErrorStringLeaf`). `Main.spec`'s named workload premises
include `grpcRepliesFit` (2026-10-31, `grpc.start`'s: the replies' encoded size). -/
theorem authkv_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [EtcdGrove.ErrorStringLeaf]
    (hD22 : ⊢ authSchemaSrv (GF := GF)) :
    etcd_auth.Main.spec (GF := GF) (hG := hG) :=
  etcd_auth.wp_Main (authkv_startServer hD22)

/-- **`Permitted(who, k)` is `permittedK who k`** (`Link.lean`'s `etcd_auth.wp_Permitted`). -/
theorem authkv_Permitted : etcd_auth.Permitted.spec (GF := GF) (hG := hG) :=
  etcd_auth.wp_Permitted

/-- **The history's check** (`Link.lean`'s `etcd_auth.wp_CheckHistory`; E2f). -/
theorem authkv_CheckHistory : etcd_auth.CheckHistory.spec (GF := GF) (hG := hG) :=
  etcd_auth.wp_CheckHistory

/-- **A range reply's check** (`Link.lean`'s `etcd_auth.wp_checkKVs`; E2f). -/
theorem authkv_checkKVs : etcd_auth.checkKVs.spec (GF := GF) (hG := hG) :=
  etcd_auth.wp_checkKVs

/-- **A transaction reply's check** (`Link.lean`'s `etcd_auth.wp_checkTxnReads`; E2f). -/
theorem authkv_checkTxnReads : etcd_auth.checkTxnReads.spec (GF := GF) (hG := hG) :=
  etcd_auth.wp_checkTxnReads

/-- **A request's context** (`Link.lean`'s `etcd_auth.wp_reqCtx`; E2f). -/
theorem authkv_reqCtx : etcd_auth.reqCtx.spec (GF := GF) (hG := hG) :=
  etcd_auth.wp_reqCtx

/-- **The set-up** (`Link.lean`'s `etcd_auth.wp_SetUp`; E2h, 5b): the puts, then the admin calls
through the client's Auth API at etcd's Auth specs (`setupAuthServed`); on success the auth
history frozen at `setupSt r`, published. -/
theorem authkv_SetUp : etcd_auth.SetUp.spec (GF := GF) (hG := hG) :=
  etcd_auth.wp_SetUp

/-- **The bad principal's request has no principal** (`ClientAuth.lean`'s `badCtx_unbound`;
E2f). -/
theorem authkv_bad_unbound (γa : auth.AuthNames) (c h : GoInterface) (a : Loc)
    (hd : etcd_auth.deliversOutgoing c h)
    (ht : metadata.mdVals (metadata.outgoingOf c) go!"token" = [etcd_auth.badToken]) :
    auth.ctxBound (GF := GF) (.on γa) h a ⊢ ⌜a = null⌝ :=
  etcd_auth.badCtx_unbound γa c h a hd ht

end results

/-- **The program's verdict is the model's at the set-up's state**, for a point request of a
non-empty key by `u` or `v` with a revision (`Model.lean`'s `granted_setupSt_iff`). -/
theorem authkv_granted_iff (rev r : Nat) (op : auth.PermType) (who k : GoString) (hr : r ≠ 0)
    (hk : k ≠ []) (hw : who = go!"u" ∨ who = go!"v") :
    auth.granted (etcd_auth.setupSt rev) ⟨who, r⟩ k [] op ↔ etcd_auth.permittedK who k :=
  etcd_auth.granted_setupSt_iff rev r op who k hr hk hw

/-- **The bad token is not the simple provider's** (`ClientAuth.lean`'s `simpleTok_ne_badToken`). -/
theorem authkv_badToken (pre : GoString) (idx : w64) : auth.simpleTok pre idx ≠ etcd_auth.badToken :=
  etcd_auth.simpleTok_ne_badToken pre idx

/-- **The bad token was issued to no one** (`ClientAuth.lean`'s `tokIssued_badToken`; E2c). -/
theorem authkv_badToken_not_issued {GF : BundledGFunctors} [AllG GF] (γa : auth.AuthNames)
    (u : GoString) : auth.tokIssued (GF := GF) γa etcd_auth.badToken u ⊢ False :=
  etcd_auth.tokIssued_badToken γa u

/-- **A token is issued to one user** (`Tokens.lean`'s `auth.tokIssued_agree`; E2c). -/
theorem authkv_token_one_user {GF : BundledGFunctors} [AllG GF] (γa : auth.AuthNames)
    (t u1 u2 : GoString) : auth.tokIssued (GF := GF) γa t u1 ∗ auth.tokIssued γa t u2 ⊢ ⌜u1 = u2⌝ :=
  auth.tokIssued_agree γa t u1 u2

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **The authentication example is safe, in the operational semantics** (`etcd_auth_adequate`,
see `Adequacy.lean`'s header for the program and the hypotheses).

**What the result does not say** (the `etcd_auth_safe` Scope's section 3):
* liveness: a run where the start, `Serve`, the client, a set-up step or a user's client fails
  returns `Failed` before any auth check runs, and the theorem holds of it;
* `Failed` at root's last `Put` and `WatchEnded` (either watch's `Collect`) skip the history's
  check (`CheckHistory`) or `u`'s watch check: that no write the auth state refuses was applied
  is checked only on runs that return `Ok` (`Collect`'s spec says nothing of the events read
  when it fails); the checks of `Work` (every refused request returned an error, every reply holds
  only keys its principal may read) have all run by then;
* a refusal is any error (`refused`): a timeout counts, not only the auth errors, so a refused
  write the server applied while the client timed out is caught only on `Ok` runs;
* not exercised: a wrong password, token expiry, admin requests by non-root users after enable,
  role or permission changes during the workload (`ErrAuthOldRevision`), auth disable, watches
  inside `[a, b)` by `v` or the unauthenticated principals, the kind of error returned; the
  set-up's puts are admitted at any revision (`SetupWrite`);
* `u`'s permitted requests need not succeed: a server that refuses every workload request still
  returns `Ok` (`authkv_test.go`'s `TestMainRun` shows they succeed in practice; the theorem does
  not);
* password checking is not verified: `bcrypt.CompareHashAndPassword`'s axiom promises nothing
  about its answer (D-AU6), so `Authenticate` may accept or refuse any password as far as the
  proof knows;
* only the simple token provider (`AuthToken = "simple"`), not JWT;
* client-certificate (TLS) authentication is off: the server's TLS identity is absent
  (`srvTLSId_false`);
* the check that a refused principal's watch reports nothing sees only the events delivered
  before `refusedWatchTimeout` (2 s);
* the history's check attributes a write to the principal its key names (`writerK`, the `who` of
  `x/<who>/…`), not to the client that sent it: sound because the workload writes only its own
  principal's keys (`keyOf x who n`), so a write of `x/<who>/…` in the history was sent by `who`
  (or is a set-up put) and checking it against `who`'s permissions checks its sender's. -/
theorem etcd_auth_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
    -- (D22) the auth store's backend with auth on: trusted text, a named hypothesis
    (hD22 : ∀ hG : HeapGS .hasLC putgetGF, ⊢ authSchemaSrv (GF := putgetGF) (hG := heapAt hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget.BootFacts id ctxs boot)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed authkvProgram authkvNames)
    (HAs : addrsUnclaimed authkvProgram [go!"127.0.0.1:23916"])
    (HDs : dataDirsAbsent authkvProgram [go!"authkv.etcd"])
    (HEnv : verifyEnvOff authkvProgram)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcd_auth.premises (GF := putgetGF) (hG := heapAt hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([authkvProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(W64 0) ∨ v = #(W64 1) ∨ v = #(W64 2)) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  etcd_auth_adequate Hctx Hcec hD22 id ctxs boot Hbf Haf Hbuq Hrf Hdbo HNs HAs HDs HEnv n Hprem
    σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms authkv_Main
#print axioms authkv_Permitted
#print axioms authkv_granted_iff
#print axioms authkv_badToken
#print axioms authkv_badToken_not_issued
#print axioms authkv_token_one_user
#print axioms authkv_CheckHistory
#print axioms authkv_checkKVs
#print axioms authkv_checkTxnReads
#print axioms authkv_reqCtx
#print axioms authkv_SetUp
#print axioms authkv_bad_unbound
#print axioms authkv_startServer
#print axioms etcd_auth_adequate
#print axioms etcd_auth_safe

end EtcdGrove
end Perennial
