/-
**The vocabulary of the auth-on interim contracts at the cluster view** (F7, `notes/etcd-dist-f7.md`; #50,
2026-11-26). Lean-first (no Rocq counterpart).

Definitions only. The fourteen contracts drafted here were adopted as interim trust-boundary axioms on 2026-11-26
(F7 S3, the lead's approval #50 06:08Z), each in its own Spec/Proof pair beside `KVPutDist.lean`: `NewUserDist`,
`KVPutOnDist`, `KVDeleteOnDist`, `TxnCommitOnDist`, `KVGetOnDist`, `AuthUserAddDist`, `AuthUserGrantRoleDist`,
`AuthRoleAddDist`, `AuthRoleGrantPermissionDist`, `AuthAuthEnableDist`, `LeaseGrantOnDist`, `LeaseRevokeOnDist`,
`LeaseTimeToLiveOnDist`, `LeaseLeasesOnDist` (reviews: `notes/axiom-review/f7-*.md`,
`f7-changed-since-review.md`).

The vocabulary (see the note, "The view"):
* the cluster's auth history is `Γ.kv.hist` (one name for every member: `etcdstart.memberGOkOn`), and the
  requested log `Γ.kv.rlog` (`srvReqLogLb γR L` at any `γR` with `γR.raft.log = Γ.kv.rlog`, the one field
  it reads);
* `Γ.au mid`, member `mid`'s auth names (`DistView.au`, F7 review A/C, 2026-11-26: until then a free binder
  `A`, which a caller could instantiate with names whose history it owns and so refute every success arm;
  `notes/axiom-review/f7-a.md`). Only the member-local facts read it (the published index
  `auth.authPubLbM`, a member's read and lease checks). They are sound only through `Serve_dist` (since F7
  step 3, 2026-11-26), whose auth-on premise `memberUpOnL … (Γ.au mid) …` holds the member's exclusive auth
  resources at `Γ.au mid`: address facts are minted for any `Γ` (`etcdAddr_set`), so Serve's premise is the
  only tie. With P-A1 (`NewServer_dist` taking `γa` from the start, as P-L1 the lessor's, F7 step 3) a start can meet it;
  `ofKV` sets it to a constant;
* **distinct names** (the lease review, `rev-f2-report.md`, 2026-11-26: `DistView.ofKV` gives every member
  the same lessor name, `ls := fun _ => 0`, which lets a fact about member A's names be used at member B):
  every contract that reads a per-member name takes `∀ a b, Γ.au a = Γ.au b → a = b` (and, where it reads
  `Γ.ls`, `∀ a b, Γ.ls a = Γ.ls b → a = b`), the lease review's form; `ofKV` fails it. Over every `w64`, not
  a member set: `DistView` has none. With Serve's tie (above) it is redundant, kept (harmless). The start
  discharges it once it allocates the names per member (P-A1, P-L1), completing the map off the members
  with names it never owns;
* a call's principal is the client's configured user name (`principalOf cfg`, from `New`'s `cfg` field),
  never a token. (Note, 2026-11-26: a simple token is NOT only its issuing member's: `EtcdServer.Authenticate`
  draws the prefix at the receiving member and proposes it through raft, and every member's apply assigns
  `<prefix>.<index>` to the same user (`tokenSimple.assign`); only its TTL keeper is per member. So a token of
  member A is accepted by B once B has applied the entry, as the same user, and rejected
  (`ErrInvalidAuthToken`) before that or after B's keeper expired it. The contracts need neither: they state
  the user, which is the same either way.)

**The lead's condition (#50, 2026-11-26T01:29:52Z), in every auth-on contract:**
* the success arm says member `mid`'s check passed for the call's user at the current auth history:
  `servedBy eps Γ mid` names the member, and the check is `writeCheckedD` (a write: granted at the history
  after a requested prefix `L ⊒ L₀`, the auth history's lower bound along `L`), `readCheckedD` (a read: the
  member's verdict at its published index, that index's state the history's after `L ⊒ L₀`), `leaseCheckD`
  (a member-local lease call), `adminRepliedD` (an admin call: admitted at the history after `L`), or
  `newCheckedD` (`New`'s password check);
* the error arm is `err ≠ nil ∧ resp = null` and claims nothing: `ErrInvalidAuthToken`, an expired token
  (the member's TTL keeper), a token another member has not yet applied, `ErrAuthOldRevision`,
  `ErrUserEmpty`, `ErrPermissionDenied` are all returned errors there, and no premise asks for a valid token
  (only `outTokOk`: the caller adds no issued token of its own, under `token` or `authorization`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientViewDist
public import Spec.go_etcd_io.etcd.client.v3.New
public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.client.v3.InvTxnBuilder
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheck
public import Proof.go_etcd_io.etcd.server.v3.auth.Reads
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthTieRead

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace authd

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The principal (pure) -/

/-- **The principal a client's calls are made as**: its configured user name, `none` for an anonymous
client (empty user name or password: `New` then authenticates nothing, `clientAuthPre_anon`). Sound only
with `cfg.Token' = []` (`userClientAt`'s premise; `clientCfgOk` asks it of `New`): a preset `cfg.Token`
is sent as is, `getToken`, and binds the calls to its user whatever `cfg.Username` says. -/
def principalOf [GooseExts] (cfg : go_etcd_io.etcd.client.v3.Config) : Option GoString :=
  if cfg.Username' = go!"" ∨ cfg.Password' = go!"" then none else some cfg.Username'

/-- **A header user a call of principal `P` can be bound to**: the empty user (no token, or auth off at
the member), or `P`'s own name. -/
def userOk (P : Option GoString) (user : GoString) : Prop :=
  user = (zeroValDef : GoString) ∨ P = some user

/-- **A context's outgoing token is no issued one**: no `token` and no `authorization` metadata, or (an
anonymous client only) values under either key none of which, its `Bearer ` prefix trimmed, has the simple
provider's shape (`auth.tokShape`: `<prefix>.<index>`), so no member issued it (authLease's `badtoken`).

Both keys (F7 S5 review, `notes/axiom-review/f7-s5-review.md` §1, 2026-11-26: until then `token` only, which
was UNSOUND): the server's `AuthInfoFromCtx` (`server/auth/store.go:1072`, `auth.mdTokenOf`) reads `token`
and, when it is absent, `authorization`, each with an optional `Bearer ` prefix trimmed; an anonymous client
sending root's token under `authorization` is served as root (Go test `notes/axiom-review/f7-s5-gotest/`). -/
def outTokOk [GooseExts] (P : Option GoString) (om : GrpcMd) : Prop :=
  (metadata.mdVals om go!"token" = [] ∧ metadata.mdVals om go!"authorization" = []) ∨
    (P = none ∧ ∀ k ∈ [go!"token", go!"authorization"], ∀ t ∈ metadata.mdVals om k,
      ¬ auth.tokShape (strings.trimPrefix t go!"Bearer "))

/-- No outgoing metadata (the contexts `New`'s and `NewClients`' clients are called with) sends no token. -/
theorem outTokOk_none [GooseExts] (P : Option GoString) : outTokOk P none := Or.inl ⟨rfl, rfl⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The member that served a call** (persistent): one of the client's endpoints `eps` is member
`mid`'s address at `Γ`. -/
def servedBy [NetProtoGS] (eps : List GoString) (Γ : DistView) (mid : w64) : IProp GF :=
  iprop(∃ a : GoString, ⌜a ∈ eps⌝ ∗ etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid)

/-- **A write's grant at the cluster, for principal `P`** (`v3rpc.opGrantT` with the token's binding
`hdrBoundT T E.authMode tok` replaced by `userOk P`: nothing of a member's tokens or TLS): the stamped
request granted after a committed prefix `L` extending `L₀`, `L`'s KV state the one the update fires at,
the auth history's lower bound along `L`. -/
def opGrantD (γk : KVNames) (P : Option GoString) : KVOp → List EntryModel → KVState → IProp GF
  | .put o, L₀ =>
    writeGrantG γk srvAuthSt0 (fun hm => iprop(⌜userOk P hm.username⌝)) (irrPut o) L₀
  | .deleteRange o, L₀ =>
    writeGrantG γk srvAuthSt0 (fun hm => iprop(⌜userOk P hm.username⌝)) (irrDeleteRange o) L₀
  | .txn t, L₀ => fun σ => iprop(∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗
      writeGrantG γk srvAuthSt0 (fun hm => iprop(⌜userOk P hm.username⌝)) (irrTxn tw) L₀ σ)
  | .leaseGrant id ttl, L₀ =>
    writeGrantG γk srvAuthSt0 (fun hm => iprop(⌜userOk P hm.username⌝)) (irrLeaseGrant id ttl) L₀
  | .leaseRevoke id, L₀ =>
    writeGrantG γk srvAuthSt0 (fun hm => iprop(⌜userOk P hm.username⌝)) (irrLeaseRevoke id) L₀
  | _, _ => fun _ => iprop(True)

/-- **The auth-on write update** (persistent: a write is resent after a token refresh, so the update may
be offered to several attempts; it fires at most once, at the entry's commit): `□ kvAu1G` at the
cluster's KV names, told the grant (`opGrantD`) at the caller's lower bound `L₀` of the requested log
(the caller's `srvReqLogLb γR L₀`, a separate premise). -/
def writeAuD (γk : KVNames) (P : Option GoString) (op : KVOp) (L₀ : List EntryModel)
    (Q : KVState → IProp GF) : IProp GF :=
  iprop(□ kvAu1G γk (kvOpStep op) (opGrantD γk P op L₀) Q)

/-- **A successful write's check** (persistent; `v3rpc.writeGrantOn` at the cluster): member `mid` of
the endpoints served it, the stamped request (header `hm`, its user one `P` may be bound to) was granted
by the auth state after the requested prefix `L ⊒ L₀` before its entry (`grantedAt`: the apply-time
permission check every member makes alike), and the auth history's lower bound along `L`. -/
def writeCheckedD [NetProtoGS] (eps : List GoString) (Γ : DistView) (γR : ServerRaftNames)
    (P : Option GoString) (rq : apply.IRRModel) (L₀ : List EntryModel) : IProp GF :=
  iprop(∃ (mid : w64) (hm : apply.HeaderModel) (L : List EntryModel), servedBy eps Γ mid ∗
    srvReqLogLb γR L ∗ authHistLb Γ.kv (admStates Γ.kv srvAuthSt0 L) ∗
    ⌜L₀ <+: L ∧ userOk P hm.username ∧ grantedAt Γ.kv srvAuthSt0 (apply.withHeader rq hm) L⌝)

/-- **What an admin call's success tells the caller** (`v3rpc.adminReplied` at the cluster: the member's
publication `pubAfterM` and the token binding dropped, the requested log in place of the committed one):
member `mid` of the endpoints served it; the stamped request, admitted and applied after the requested
prefix `L` (`adminDoneM`: `auth.adminOk` at the history's last state along `L`), its result (`adminQh`: the
history update's `Q`), its header's user one `P` may be bound to. -/
def adminRepliedD [NetProtoGS] (eps : List GoString) (Γ : DistView) (γR : ServerRaftNames)
    (P : Option GoString) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ (mid : w64) (hm : apply.HeaderModel) (rq' : apply.IRRModel) (L : List EntryModel),
    servedBy eps Γ mid ∗
    ⌜irrWireOf (apply.withHeader rq hm) rq' ∧ adminDoneM true Γ.kv rq' L ∧ userOk P hm.username⌝ ∗
    srvReqLogLb γR L ∗ adminQh Γ.kv rq Q hm L)

/-- **What a successful auth-on read tells the caller of its check, cluster-level**: the principal it
was bound to may read `[key, end)` at the auth state after the requested prefix `L` extending `L₀`
(`readCheckedD` gives `srvReqLogLb γR L` with it: `L` is committed; re-review A's N1, 2026-11-26). -/
def readAuthedD (γk : KVNames) (P : Option GoString) (L₀ L : List EntryModel) (o : OpFull) : Prop :=
  ∃ (user e : GoString) (rv : Nat), userOk P user ∧ L₀ <+: L ∧
    apply.authEndOf o.base.rangeEnd e ∧
    auth.permitted (srvAuthAtLog γk srvAuthSt0 L) ⟨user, rv⟩ o.key e .read

/-- **Member `mid`'s published auth index is at least `m`, its state at an index `i ≤ m` is the
history's after a requested prefix `L ⊒ L₀`, and so is every state it records from `i` on**
(persistent; `authFloorAt` at the cluster, over the requested log): the floor a linearizable read's
barrier leaves (`KV_GetOn_dist`), which a member-local lease check at `Γ.au mid` needs.

The last conjunct (F7 S5, 2026-11-26, the lead's approval #50 06:35Z; the shape `KV_GetOn_dist`'s
`readCheckedD` has after N1): every state the member's apply thread records at an index `j ≥ i` is the
history's after a committed prefix `L' ⊒ L₀` of the cluster's one requested log (`srvReqLogLb γR L'`).
Why it holds of etcd (`notes/axiom-review/f7-getOn-n1.md`, retirement obligation R1): each recorded state is
`authHistTie`'s, `srvAuthAtLog` of a committed log (`isServerReadM_tie`), the member's history a prefix of
the cap `bootState :: admStates ρ.kv st₀ A` (`authOwn_capped`); a position at or after the floor's is the
floor's state (`L' := L`) or the state after a later admin entry of `A` (`L'` the prefix of `A` through it,
which extends `L`). It is what a later member-local lease check at index `≥ m` (`leaseCheckD`) is read
against: the cross-machine form of the single-process `akAuthFixed`.

Under a fancy update at a mask holding `authTieReadMask` (F7 S5 review, `notes/axiom-review/f7-s5-review.md`
§2.2, 2026-11-26: until then a plain persistent wand, false in the logic: the log fragment `srvReqLogLb γR L'`
of a state recorded after the floor exists only inside the tie's invariant `authTieN`, so it is obtained by
opening it, as `akAuthFixed` states, `examples/etcd/auth/WorkEnv.lean`). -/
def authFloorD (Γ : DistView) (γR : ServerRaftNames) (mid : w64)
    (L₀ : List EntryModel) (m : Nat) : IProp GF :=
  iprop(auth.authPubLbM (.on (Γ.au mid)) m ∗ ∃ (L : List EntryModel) (i : Nat), ⌜L₀ <+: L ∧ i ≤ m⌝ ∗
    srvReqLogLb γR L ∗ auth.authStateAt (Γ.au mid) i (srvAuthAtLog Γ.kv srvAuthSt0 L) ∗
    □ (∀ (E' : CoPset) (j : Nat) (st : auth.AuthState), ⌜authTieReadMask ⊆ E' ∧ i ≤ j⌝ -∗
      auth.authStateAt (Γ.au mid) j st ={E'}=∗
      ∃ L' : List EntryModel, ⌜L₀ <+: L' ∧ st = srvAuthAtLog Γ.kv srvAuthSt0 L'⌝ ∗ srvReqLogLb γR L'))

/-- **A successful linearizable range's check** (persistent; `v3rpc.rangeAuthed` at the cluster):
member `mid` of the endpoints served it, its verdict (`rangeClassFrom`) passed for `info` at its auth
state of index `m` (published, `authFloorD`'s floor above `L₀`), `info`'s user one `P` may be bound to; and
the cluster-level check (`readAuthedD`) at a requested prefix `L ⊒ L₀` that is a lower bound of the
requested log (`srvReqLogLb γR L`, re-review A's N1, 2026-11-26: so `L` is committed, not any extension). -/
def readCheckedD [NetProtoGS] (eps : List GoString) (Γ : DistView)
    (γR : ServerRaftNames) (P : Option GoString) (L₀ : List EntryModel) (o : OpFull) : IProp GF :=
  iprop(∃ (mid : w64) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat) (L : List EntryModel),
    servedBy eps Γ mid ∗ ⌜userOk P info.Username' ∧ readAuthedD Γ.kv P L₀ L o⌝ ∗ srvReqLogLb γR L ∗
    apply.rangeClassFrom (.on (Γ.au mid)) m info o ∗ authFloorD Γ γR mid L₀ m)

/-- **A successful read-only transaction's check** (`readCheckedD`'s, at `txnClassFrom`: every
range of the transaction, nested ones included, checked at the member's state `m`). -/
def txnReadCheckedD [NetProtoGS] (eps : List GoString) (Γ : DistView)
    (γR : ServerRaftNames) (P : Option GoString) (L₀ : List EntryModel) (t : TxnModel) : IProp GF :=
  iprop(∃ (mid : w64) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat),
    servedBy eps Γ mid ∗ ⌜userOk P info.Username'⌝ ∗
    txnClassFrom (.on (Γ.au mid)) m info t ∗ authFloorD Γ γR mid L₀ m)

/-- **A member-local lease call's check at `γa` and index `n`** (`leaseCheckFrom` with the binding
`principalBound T E.authMode tok` replaced by `P = some info.Username'`): auth disabled at a state of index
at least `n`, or the call's `info`, `P`'s own user, an admin there or passing `K`.

The binding is `requireAuthInfo`'s (`v3_server.go`: with auth enabled a nil `AuthInfo` is refused,
`ErrUserEmpty`; a non-nil one comes from an accepted token, which `New` obtained for `cfg`'s user), so an
anonymous principal (`P = none`) never passes the second arm (F7 S5, 2026-11-26, the lead's approval #50
06:35Z: until then `userOk P`, which admits the empty user and made the arm vacuous for `P = none`,
`notes/axiom-review/f7-c.md`). -/
def leaseCheckD (γa : auth.AuthNames) (P : Option GoString) (n : Nat)
    (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) : IProp GF :=
  iprop(auth.enabledVerdictFrom (.on γa) n false ∨
    ∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, ⌜P = some info.Username'⌝ ∗
      (auth.adminVerdictFrom (.on γa) n info GoInterface.nil ∨ K info))

/-- **What every auth-on KV contract takes of the client**: `kvClientAt`'s (its `KV` the `*kv` `api`),
and its configuration `cfg`, read-only (whose user name is the principal), with no preset token. -/
def userClientAt [NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) : IProp GF :=
  iprop(kvClientAt cl api eps V Γ ∗ clientF cl go!"cfg" ↦□ cfg ∗ ⌜cfg.Token' = []⌝)

/-- **An auth client of the view**: `New`'s client of endpoints serving `Γ`, with no proxy, its `Auth`
field the `*authClient` `ap`, its configuration `cfg` (no preset token). -/
def authClientAt [NetProtoGS] (cl ap : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) : IProp GF :=
  iprop(isNewClient cl eps V ∗ clientNoProxy cl ∗ clientF cl go!"cfg" ↦□ cfg ∗ ⌜cfg.Token' = []⌝ ∗
    clientF cl go!"Auth" ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty) #ap : GoInterface) ∗
    membersAt (Gg := hG.goose_globalGS) eps Γ)

/-- **A lease client of member `mid`, auth on**: F2's `view.leaseClientAt` (one endpoint `ep` serving
`mid`, the `Lease` field `lp`), and its configuration `cfg` (no preset token). -/
def leaseUserAt [NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (cfg : go_etcd_io.etcd.client.v3.Config) : IProp GF :=
  iprop(view.leaseClientAt cl lp ep V Γ mid ∗ clientF cl go!"cfg" ↦□ cfg ∗ ⌜cfg.Token' = []⌝)

end defs

end authd
end etcd_dist
end EtcdGrove
end Perennial
