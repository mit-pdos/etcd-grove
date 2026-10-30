/-
The authentication example's results (`examples/authkv/authkv.go`; the auth plan's E2b), restated,
with the trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq
counterpart).

* **`authkv_Main`** (`Link.lean`'s `authkv.wp_Main`): `Main()` -- one member with the simple token
  provider, auth set up and enabled, four principals' workloads inside and outside `[a, b)`, and
  checks that panic if the server let a principal do what the auth state does not permit -- does
  not panic and returns `Ok`, `Failed` or `WatchEnded` (`Spec/.../authkv/Main.lean`). **Not proved:
  a `sorry`** (`Main.lean` lists what its proof needs).
* **`authkv_Permitted`** (`Link.lean`'s `authkv.wp_Permitted`): the program's verdict
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
  `server_new_auth_on` (its named premises: `isValidSimpleToken`'s spec, D22's `authSchemaSrv`) and
  `server_Start_on`.
* **`authkv_SetUp`** (`Link.lean`'s `authkv.wp_SetUp`; E2h, the auth-mode merge's 5b): `SetUp`,
  through a client with no user, at etcd's Auth specs, from the client's view of the auth history:
  on success the history frozen at a log whose auth state is `setupSt r`, published.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.startServer
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Results

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- **`Main` does not panic** (`Link.lean`'s `authkv.wp_Main`; not proved: a `sorry`). At the
hypothesis on the semantics every client-building `Main` has (`DialWithBalancerBody`, through
`newUserClient`'s `clientv3.New`; watchkv's, cachekv's, ...). -/
theorem authkv_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    authkv.Main.spec (GF := GF) (hG := hG) :=
  authkv.wp_Main

/-- **`Permitted(who, k)` is `permittedK who k`** (`Link.lean`'s `authkv.wp_Permitted`). -/
theorem authkv_Permitted : authkv.Permitted.spec (GF := GF) (hG := hG) :=
  authkv.wp_Permitted

/-- **The history's check** (`Link.lean`'s `authkv.wp_CheckHistory`; E2f). -/
theorem authkv_CheckHistory : authkv.CheckHistory.spec (GF := GF) (hG := hG) :=
  authkv.wp_CheckHistory

/-- **A range reply's check** (`Link.lean`'s `authkv.wp_checkKVs`; E2f). -/
theorem authkv_checkKVs : authkv.checkKVs.spec (GF := GF) (hG := hG) :=
  authkv.wp_checkKVs

/-- **A transaction reply's check** (`Link.lean`'s `authkv.wp_checkTxnReads`; E2f). -/
theorem authkv_checkTxnReads : authkv.checkTxnReads.spec (GF := GF) (hG := hG) :=
  authkv.wp_checkTxnReads

/-- **A request's context** (`Link.lean`'s `authkv.wp_reqCtx`; E2f). -/
theorem authkv_reqCtx : authkv.reqCtx.spec (GF := GF) (hG := hG) :=
  authkv.wp_reqCtx

/-- **The set-up** (`Link.lean`'s `authkv.wp_SetUp`; E2h, 5b): the puts, then the admin calls
through the client's Auth API at etcd's Auth specs (`setupAuthServed`); on success the auth
history frozen at `setupSt r`, published. -/
theorem authkv_SetUp : authkv.SetUp.spec (GF := GF) (hG := hG) :=
  authkv.wp_SetUp

/-- **The bad principal's request has no principal** (`ClientAuth.lean`'s `badCtx_unbound`;
E2f). -/
theorem authkv_bad_unbound (γa : auth.AuthNames) (c h : GoInterface) (a : Loc)
    (hd : authkv.deliversOutgoing c h)
    (ht : metadata.mdVals (metadata.outgoingOf c) go!"token" = [authkv.badToken]) :
    auth.ctxBound (GF := GF) (.on γa) h a ⊢ ⌜a = null⌝ :=
  authkv.badCtx_unbound γa c h a hd ht

/-- **The member started with auth on** (`startServer.lean`; E3zb): `NewServer.specM true`
(`server_new_auth_on`, with its named premises) and `Start.specOn` (`server_Start_on`). -/
theorem authkv_startServer [EtcdGrove.Float64ToInt64Semantics] [EtcdGrove.ErrorStringLeaf]
    (hValid : auth.ValidSpec (GF := GF) (hG := hG)) (hD22 : ⊢ authSchemaSrv (GF := GF)) :
    authkv.startServer.spec (GF := GF) (hG := hG) :=
  authkv.startServer.wp_proof common.features.wp_NewDefaultServerFeatureGate
    (server_new_auth_on hValid hD22) server_Start_on

end results

/-- **The program's verdict is the model's at the set-up's state**, for a point request of a
non-empty key by `u` or `v` with a revision (`Model.lean`'s `granted_setupSt_iff`). -/
theorem authkv_granted_iff (rev r : Nat) (op : auth.PermType) (who k : GoString) (hr : r ≠ 0)
    (hk : k ≠ []) (hw : who = go!"u" ∨ who = go!"v") :
    auth.granted (authkv.setupSt rev) ⟨who, r⟩ k [] op ↔ authkv.permittedK who k :=
  authkv.granted_setupSt_iff rev r op who k hr hk hw

/-- **The bad token is not the simple provider's** (`ClientAuth.lean`'s `simpleTok_ne_badToken`). -/
theorem authkv_badToken (pre : GoString) (idx : w64) : auth.simpleTok pre idx ≠ authkv.badToken :=
  authkv.simpleTok_ne_badToken pre idx

/-- **The bad token was issued to no one** (`ClientAuth.lean`'s `tokIssued_badToken`; E2c). -/
theorem authkv_badToken_not_issued {GF : BundledGFunctors} [AllG GF] (γa : auth.AuthNames)
    (u : GoString) : auth.tokIssued (GF := GF) γa authkv.badToken u ⊢ False :=
  authkv.tokIssued_badToken γa u

/-- **A token is issued to one user** (`Tokens.lean`'s `auth.tokIssued_agree`; E2c). -/
theorem authkv_token_one_user {GF : BundledGFunctors} [AllG GF] (γa : auth.AuthNames)
    (t u1 u2 : GoString) : auth.tokIssued (GF := GF) γa t u1 ∗ auth.tokIssued γa t u2 ⊢ ⌜u1 = u2⌝ :=
  auth.tokIssued_agree γa t u1 u2

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

end EtcdGrove
end Perennial
