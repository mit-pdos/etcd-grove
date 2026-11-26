/-
**DRAFTS of the auth-on interim contracts at the cluster view** (F7, `notes/etcd-dist-f7.md`; #50, 2026-11-26).
Lean-first (no Rocq counterpart).

STATEMENTS ONLY: definitions, no axiom, no proof, no `sorry`. Nothing imports this file. Each draft
`X.spec` becomes `axiom X.wp_proof : X.spec` in its own Spec/Proof pair beside `KVPutDist.lean` only after
a fresh `axiom`-skill review (`notes/etcd-dist-f7-reviews.md`), and joins the etcd_safe packet.

The vocabulary (see the note, "The view"):
* the cluster's auth history is `Γ.kv.hist` (one name for every member: `etcdstart.memberGOkOn`), and the
  requested log `Γ.kv.rlog` (`srvReqLogLb γR L` at any `γR` with `γR.raft.log = Γ.kv.rlog`, the one field
  it reads);
* `A : w64 → auth.AuthNames`, member `mid`'s auth names (joins `DistView` as `au` at implementation, with
  the Prove item P-A1, `NewServer` taking `γa` from the start as P-L1 takes the lessor's); only the member-local
  facts read it (the published index `auth.authPubLbM`, a member's read and lease checks);
* **distinct names** (the lease review, `rev-f2-report.md`, 2026-11-26: `DistView.ofKV` gives every member
  the same lessor name, `ls := fun _ => 0`, which lets a fact about member A's names be used at member B):
  every draft that reads a per-member name takes `∀ a b, A a = A b → a = b` (and, where it reads `Γ.ls`,
  `∀ a b, Γ.ls a = Γ.ls b → a = b`), the lease review's form; `ofKV` fails it. Over every `w64`, not a member
  set: `DistView` has none. The start discharges it once it allocates the names per member (P-A1, P-L1),
  completing the map off the members with names it never owns;
* a call's principal is the client's configured user name (`principalOf cfg`, from `New`'s `cfg` field),
  never a token. (Note, 2026-11-26: a simple token is NOT only its issuing member's: `EtcdServer.Authenticate`
  draws the prefix at the receiving member and proposes it through raft, and every member's apply assigns
  `<prefix>.<index>` to the same user (`tokenSimple.assign`); only its TTL keeper is per member. So a token of
  member A is accepted by B once B has applied the entry, as the same user, and rejected
  (`ErrInvalidAuthToken`) before that or after B's keeper expired it. The contracts need neither: they state
  the user, which is the same either way.)

**The lead's condition (#50, 2026-11-26T01:29:52Z), in every auth-on draft:**
* the success arm says member `mid`'s check passed for the call's user at the current auth history:
  `servedBy eps Γ mid` names the member, and the check is `writeCheckedD` (a write: granted at the history
  after a requested prefix `L ⊒ L₀`, the auth history's lower bound along `L`), `readCheckedD` (a read: the
  member's verdict at its published index, that index's state the history's after `L ⊒ L₀`), `leaseCheckD`
  (a member-local lease call), `adminRepliedD` (an admin call: admitted at the history after `L`), or
  `newCheckedD` (`New`'s password check);
* the error arm is `err ≠ nil ∧ resp = null` and claims nothing: `ErrInvalidAuthToken`, an expired token
  (the member's TTL keeper), a token another member has not yet applied, `ErrAuthOldRevision`,
  `ErrUserEmpty`, `ErrPermissionDenied` are all returned errors there, and no premise asks for a valid token
  (only `outTokOk`: the caller adds no issued token of its own).
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

/-- **A context's outgoing token is no issued one**: no `token` metadata, or (an anonymous client only)
values none of which has the simple provider's shape (`auth.tokShape`: `<prefix>.<index>`), so no member
issued it (authLease's `badtoken`). -/
def outTokOk [GooseExts] (P : Option GoString) (om : GrpcMd) : Prop :=
  metadata.mdVals om go!"token" = [] ∨
    (P = none ∧ ∀ t ∈ metadata.mdVals om go!"token", ¬ auth.tokShape t)

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
was bound to may read `[key, end)` at the auth state after a requested prefix `L` extending `L₀`. -/
def readAuthedD (γk : KVNames) (P : Option GoString) (L₀ : List EntryModel) (o : OpFull) : Prop :=
  ∃ (user e : GoString) (rv : Nat) (L : List EntryModel), userOk P user ∧ L₀ <+: L ∧
    apply.authEndOf o.base.rangeEnd e ∧
    auth.permitted (srvAuthAtLog γk srvAuthSt0 L) ⟨user, rv⟩ o.key e .read

/-- **Member `mid`'s published auth index is at least `m`, and its state at an index `i ≤ m` is the
history's after a requested prefix `L ⊒ L₀`** (persistent; `authFloorAt` at the cluster, over the
requested log): the floor a linearizable read's barrier leaves (`KV_GetOn_dist`), which a member-local
lease check at `A mid` needs. -/
def authFloorD (A : w64 → auth.AuthNames) (Γ : DistView) (γR : ServerRaftNames) (mid : w64)
    (L₀ : List EntryModel) (m : Nat) : IProp GF :=
  iprop(auth.authPubLbM (.on (A mid)) m ∗ ∃ (L : List EntryModel) (i : Nat), ⌜L₀ <+: L ∧ i ≤ m⌝ ∗
    srvReqLogLb γR L ∗ auth.authStateAt (A mid) i (srvAuthAtLog Γ.kv srvAuthSt0 L))

/-- **A successful linearizable range's check** (persistent; `v3rpc.rangeAuthed` at the cluster):
member `mid` of the endpoints served it, its verdict (`rangeClassFrom`) passed for `info` at its auth
state of index `m` (published, `authFloorD`'s floor above `L₀`), `info`'s user one `P` may be bound to; and
the cluster-level check (`readAuthedD`). -/
def readCheckedD [NetProtoGS] (eps : List GoString) (A : w64 → auth.AuthNames) (Γ : DistView)
    (γR : ServerRaftNames) (P : Option GoString) (L₀ : List EntryModel) (o : OpFull) : IProp GF :=
  iprop(∃ (mid : w64) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat),
    servedBy eps Γ mid ∗ ⌜userOk P info.Username' ∧ readAuthedD Γ.kv P L₀ o⌝ ∗
    apply.rangeClassFrom (.on (A mid)) m info o ∗ authFloorD A Γ γR mid L₀ m)

/-- **A successful read-only transaction's check** (`readCheckedD`'s, at `txnClassFrom`: every
range of the transaction, nested ones included, checked at the member's state `m`). -/
def txnReadCheckedD [NetProtoGS] (eps : List GoString) (A : w64 → auth.AuthNames) (Γ : DistView)
    (γR : ServerRaftNames) (P : Option GoString) (L₀ : List EntryModel) (t : TxnModel) : IProp GF :=
  iprop(∃ (mid : w64) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat),
    servedBy eps Γ mid ∗ ⌜userOk P info.Username'⌝ ∗
    txnClassFrom (.on (A mid)) m info t ∗ authFloorD A Γ γR mid L₀ m)

/-- **A member-local lease call's check at `γa` and index `n`** (`leaseCheckFrom` with the binding
`principalBound T E.authMode tok` replaced by `userOk P`): auth disabled at a state of index at least `n`,
or the call's `info` (its user one `P` may be bound to) an admin there or passing `K`. -/
def leaseCheckD (γa : auth.AuthNames) (P : Option GoString) (n : Nat)
    (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) : IProp GF :=
  iprop(auth.enabledVerdictFrom (.on γa) n false ∨
    ∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, ⌜userOk P info.Username'⌝ ∗
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

/-! ## The drafts -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-! ### `New` -/

/-- **DRAFT `New_user_dist`: `clientv3.New(cfg)` with a user name, across machines** (mirrors
`clientv3.New.spec`, whose `clientAuthPre` registration of `Authenticate` at `eps` is replaced by the
address facts of an auth-on view; `clientTokAt` dropped from the post: the contracts read the principal
from `cfg`). `New` calls `getToken`, one `Auth.Authenticate` over the balanced connection: a success
names the member `mid` that answered and its check, `CheckPassword`'s (`auth.passwordChecked`: auth
enabled, the user in a recorded state), or `ErrAuthNotEnabled`, which `getToken` turns into a success
with no token (`enabledVerdict … false`). A wrong password, an unknown user and every transport failure
are the error arm. -/
abbrev New_user_dist.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] [NetProtoGS] (cfg : go_etcd_io.etcd.client.v3.Config)
    (eps : List GoString) (V : WEnv GF) (Γ : DistView) (A : w64 → auth.AuthNames),
  (∀ a b : w64, A a = A b → a = b) →
  Γ.auth = true → principalOf cfg = some cfg.Username' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ levelTok 0 ∗
      clientCfgOk cfg eps ∗ ⌜strsSizeOk [cfg.Username', cfg.Password']⌝ ∗
      membersAt (Gg := hG.goose_globalGS) eps Γ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.New)) (Val #cfg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ isNewClient cl eps V ∗ clientF cl go!"cfg" ↦□ cfg ∗
          ∃ (mid : w64) (rev : w64), servedBy eps Γ mid ∗
            (auth.passwordChecked (.on (A mid)) cfg.Username' rev GoInterface.nil ∨
              auth.enabledVerdict (.on (A mid)) false)) ∨
        ⌜err ≠ GoInterface.nil ∧ cl = null⌝) }}

/-! ### KV writes -/

/-- **DRAFT `KV_PutOn_dist`: `(*kv).Put(ctx, key, val, opts...)` across machines, auth on** (mirrors
`client.client_put_on` at the cluster: `etcdPutSpecOn`'s registration replaced by `kvClientAt` at `Γ`, the
member's floor `F` dropped, the update persistent (`writeAuD`: a write is resent after
`ErrInvalidAuthToken`'s token refresh, `isSafeRetryMutableRPC` does not apply), the token's binding replaced
by the principal of `cfg`; a success tells the member and its grant, `writeCheckedD`; the error arm claims
nothing). A lease `0`, or the revocable lease mode, as `etcdPutSpecOn`'s filter: this is also F2's
`KV_PutLease_dist` row (`Put` with `WithLease(id)`, auth on), at `leaseID ≠ 0`; the lease's attach is
`kvOpStep`'s (the update's `Q` sees it), its absence `ErrLeaseNotFound` (a refusal, no step). -/
abbrev KV_PutOn_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (key val : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      userClientAt cl api eps V Γ cfg ∗ metadata.outMD ctx om ∗ srvReqLogLb γR L₀ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ (opPutModel key val opts).putPanics ∧ (opPutModel key val opts).t = W64 2 ∧
        ((putWireOf (opPutModel key val opts)).leaseID = W64 0 ∨ Γ.kv.lm = .revocable)⌝ ∗
      writeAuD Γ.kv (principalOf cfg) (.put (putWireOf (opPutModel key val opts))) L₀ Q ∗
      ⌜opSizeOk (opPutModel key val opts)⌝ }}
    (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #val)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
        ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ kvRevFits (σ.rev + 1) ∧ kvLogOk σ⌝ ∗
        kvRevLb Γ.kv m.hdr.revision ∗
        writeCheckedD eps Γ γR (principalOf cfg) (irrPut (putWireOf (opPutModel key val opts))) L₀) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `KV_DeleteOn_dist`: `(*kv).Delete(ctx, key, opts...)` across machines, auth on** (mirrors
`client.client_delete_on` at the cluster, in `KV_Delete_dist`'s statement: the update persistent
(`writeAuD`), the principal of `cfg`, a success's grant `writeCheckedD`; the error arm claims nothing). -/
abbrev KV_DeleteOn_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      userClientAt cl api eps V Γ cfg ∗ metadata.outMD ctx om ∗ srvReqLogLb γR L₀ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ opDeletePanics key opts ∧ (opDeleteModel key opts).t = W64 3 ∧
        (deleteWireOf (opDeleteModel key opts)).base.rangeEnd ≠ [W8 0]⌝ ∗
      writeAuD Γ.kv (principalOf cfg) (.deleteRange (deleteWireOf (opDeleteModel key opts))) L₀ Q ∗
      ⌜opSizeOk (opDeleteModel key opts)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Delete")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : DelRespM) (σ : KVState), delRespMsg resp m ∗ Q σ ∗
        ⌜m.deleted = W64 ((rangeIn σ.kvs (deleteWireOf (opDeleteModel key opts))).length : Int) ∧
          m.prevs = (if (deleteWireOf (opDeleteModel key opts)).base.prevKV then
            rangeIn σ.kvs (deleteWireOf (opDeleteModel key opts)) else []) ∧
          m.hdr.revision =
            W64 ((kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ).rev : Int) ∧
          kvRevFits (σ.rev + 1) ∧ kvLogOk σ ∧
          kvLogOk (kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ)⌝ ∗
        writeCheckedD eps Γ γR (principalOf cfg)
          (irrDeleteRange (deleteWireOf (opDeleteModel key opts))) L₀) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Txn_CommitOn_dist`: `(*txn).Commit()` across machines, auth on** (mirrors
`client.client_txn_on` at the cluster, in `Txn_Commit_dist`'s statement; linearizable only:
`txnSerializable = false` in the read-only case). A read-only transaction's update is `□ AU` (resent at the
next endpoint on `Unavailable`), its success the member's check (`txnReadCheckedD`); a writing one's is
`writeAuD` (resent after a token refresh), its success the grant of `irrTxn` (`writeCheckedD`, nested
operations included). The error arm claims nothing. -/
abbrev Txn_CommitOn_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl api txn_ptr : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (A : w64 → auth.AuthNames) (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (L₀ : List EntryModel) (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd)
    (b : TxnBuild) (Q : KVState → IProp GF),
  (∀ a b : w64, A a = A b → a = b) →
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      userClientAt cl api eps V Γ cfg ∗ metadata.outMD ctx om ∗ srvReqLogLb γR L₀ ∗
      txnObjAt txn_ptr eps ctx ctx_desc b ∗ txnKvIs txn_ptr api ∗
      ⌜TxnModel.plain b.model ∧ txnModelIn (txnWireOf b.model)⌝ ∗
      ((⌜txn.txnReadonly (txnWireOf b.model) = true ∧ txn.txnSerializable (txnWireOf b.model) = false⌝ ∗
          □ AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
            <{ etcdKV Γ.kv σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) ∨
        (⌜txn.txnReadonly (txnWireOf b.model) = false ∧ txn.txnPlain (txnWireOf b.model) ∧
            txnNoZeroEnd (txnWireOf b.model)⌝ ∗
          writeAuD Γ.kv (principalOf cfg) (.txn (txnWireOf b.model)) L₀ Q)) ∗
      ⌜txnSizeOk (txnWireOf b.model)⌝ }}
    (App (Val (txn_ptr @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
      (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗
        (if txn.txnReadonly (txnWireOf b.model) then iprop(□ Q σ) else Q σ) ∗
        ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf b.model)).1 ∧
          opRespsRel false ((txnWireOf b.model).branch m.succeeded)
            (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf b.model)).2.2 m.resps ∧
          m.hdr.revision = W64 ((if txn.txnReadonly (txnWireOf b.model) then σ.rev else
            (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
              (txnWireOf b.model)).2.1).rev : Nat) : Int) ∧
          kvRevFits σ.rev ∧ kvLogOk σ ∧
          (txn.txnReadonly (txnWireOf b.model) = false →
            kvLogOk (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
              (txnWireOf b.model)).2.1))⌝ ∗
        client.txnRevLb Γ.kv (txnWireOf b.model) m ∗
        (if txn.txnReadonly (txnWireOf b.model) then
          txnReadCheckedD eps A Γ γR (principalOf cfg) L₀ (txnWireOf b.model)
        else iprop(∃ tw : txn.TxnModelW, ⌜tw.toModel = txnWireOf b.model⌝ ∗
          writeCheckedD eps Γ γR (principalOf cfg) (irrTxn tw) L₀))) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-! ### KV read -/

/-- **DRAFT `KV_GetOn_dist`: `(*kv).Get(ctx, key, opts...)` across machines, auth on** (`KV_Get_dist`'s
statement, for an auth-on view, at the principal of `cfg`; a success also names the member `mid` that
served it and its check (`readCheckedD`): its verdict at its published auth index `m`, whose state is the
history's after a requested prefix `L ⊒ L₀` (the barrier's floor, `authFloorD`: a linearizable read's
check is no older than its read index, which is at least every commit before the call), and the
cluster-level `readAuthedD`). Serializable reads are not covered (no workload sends one with auth on):
`serializable = false` is a premise. -/
abbrev KV_GetOn_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (A : w64 → auth.AuthNames) (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (L₀ : List EntryModel)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF),
  (∀ a b : w64, A a = A b → a = b) →
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      userClientAt cl api eps V Γ cfg ∗ metadata.outMD ctx om ∗ srvReqLogLb γR L₀ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAtRes opts_sl opts R ∗ R ∗
      sortNamesIf (opGetModel key opts).base.sortSet ∗
      ⌜¬ opGetPanics opts ∧ (opGetModel key opts).t = W64 1 ∧
        (rangeWireOf (opGetModel key opts)).base.serializable = false⌝ ∗
      □ (⌜Q = fun _ => iprop(True)⌝ ∨
        AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) ∗
      ⌜opSizeOk (opGetModel key opts)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Get")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (R ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗ □ Q σ ∗
          ⌜sint.Z (rangeWireOf (opGetModel key opts)).base.rev ≤ (σ.rev : Int) ∧
            txn.srvRangeOk (rangeWireOf (opGetModel key opts))
              (σ.at (σ.readRev (rangeWireOf (opGetModel key opts)).base.rev)).kvs m.kvs m.more ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev ∧ kvLogOk σ⌝ ∗
          readCheckedD eps A Γ γR (principalOf cfg) L₀ (rangeWireOf (opGetModel key opts))) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝)) }}

/-! ### Admin calls (sent by the set-up's anonymous client; stated for either auth mode of the history) -/

/-- **DRAFT `Auth_UserAdd_dist`: `(*authClient).UserAdd(ctx, name, pw)` across machines** (mirrors
`authClient.UserAdd.spec` at `etcdUserAddSpecW`: the caller's persistent history update `histAu` at the
cluster's names, the binding `userOk` of `cfg`'s principal; a success the cluster-level `adminRepliedD`,
which names the member). -/
abbrev Auth_UserAdd_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl ap : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (name pw : GoString)
    (Q : List auth.AuthState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      authClientAt cl ap eps V Γ cfg ∗ metadata.outMD ctx om ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ ⌜strsSizeOk [name, pw]⌝ ∗
      (∀ um : apply.UserAddModel, ⌜um.name = name ∧ um.noPassword = false⌝ -∗
        histAu γR Γ.kv srvAuthSt0 (fun hm => iprop(⌜userOk (principalOf cfg) hm.username⌝))
          (irrUserAdd um) Q) }}
    (App (App (App (Val (ap @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!!
        go!"UserAdd")) (Val #(GoInterface.ok ctx))) (Val #name)) (Val #pw))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ um : apply.UserAddModel,
          ⌜um.name = name ∧ um.noPassword = false ∧ um.pwSure⌝ ∗
          adminRepliedD eps Γ γR (principalOf cfg) (irrUserAdd um) Q) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Auth_UserGrantRole_dist`: `(*authClient).UserGrantRole(ctx, user, role)` across machines**
(mirrors `authClient.UserGrantRole.spec` at `etcdUserGrantRoleSpecW`, as `Auth_UserAdd_dist`, at
`irrUserGrantRole user role`; the server's name bound `user.length ≤ maxKeySize` a premise). -/
abbrev Auth_UserGrantRole_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl ap : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (user role : GoString)
    (Q : List auth.AuthState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      authClientAt cl ap eps V Γ cfg ∗ metadata.outMD ctx om ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗
      ⌜strsSizeOk [user, role] ∧ user.length ≤ backend.maxKeySize⌝ ∗
      histAu γR Γ.kv srvAuthSt0 (fun hm => iprop(⌜userOk (principalOf cfg) hm.username⌝))
        (irrUserGrantRole user role) Q }}
    (App (App (App (Val (ap @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!!
        go!"UserGrantRole")) (Val #(GoInterface.ok ctx))) (Val #user)) (Val #role))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗
          adminRepliedD eps Γ γR (principalOf cfg) (irrUserGrantRole user role) Q) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Auth_RoleAdd_dist`: `(*authClient).RoleAdd(ctx, name)` across machines** (mirrors
`authClient.RoleAdd.spec` at `etcdRoleAddSpecW`, as `Auth_UserAdd_dist`, at `irrRoleAdd name`). -/
abbrev Auth_RoleAdd_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl ap : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (name : GoString)
    (Q : List auth.AuthState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      authClientAt cl ap eps V Γ cfg ∗ metadata.outMD ctx om ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗
      ⌜strsSizeOk [name] ∧ name.length ≤ backend.maxKeySize⌝ ∗
      histAu γR Γ.kv srvAuthSt0 (fun hm => iprop(⌜userOk (principalOf cfg) hm.username⌝))
        (irrRoleAdd name) Q }}
    (App (App (Val (ap @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!!
        go!"RoleAdd")) (Val #(GoInterface.ok ctx))) (Val #name))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ adminRepliedD eps Γ γR (principalOf cfg) (irrRoleAdd name) Q) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Auth_RoleGrantPermission_dist`: `(*authClient).RoleGrantPermission(ctx, name, key,
rangeEnd, permType)` across machines** (mirrors `authClient.RoleGrantPermission.spec` at
`etcdRoleGrantPermissionSpecW`, as `Auth_UserAdd_dist`, at `irrRoleGrantPermission name (some w)` with
`w = ⟨permType, key, rangeEnd⟩`; the client's key bound and the server's name bound premises). -/
abbrev Auth_RoleGrantPermission_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl ap : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd)
    (name key rangeEnd : GoString) (permType : w32) (Q : List auth.AuthState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      authClientAt cl ap eps V Γ cfg ∗ metadata.outMD ctx om ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗
      ⌜strsSizeOk [name, key, rangeEnd] ∧ key.length < 2 ^ 63 - 1 ∧
        name.length ≤ backend.maxKeySize⌝ ∗
      histAu γR Γ.kv srvAuthSt0 (fun hm => iprop(⌜userOk (principalOf cfg) hm.username⌝))
        (irrRoleGrantPermission name (some ⟨permType, key, rangeEnd⟩)) Q }}
    (App (App (App (App (App (Val (ap @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!!
        go!"RoleGrantPermission")) (Val #(GoInterface.ok ctx))) (Val #name)) (Val #key))
        (Val #rangeEnd)) (Val #permType))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ adminRepliedD eps Γ γR (principalOf cfg)
          (irrRoleGrantPermission name (some ⟨permType, key, rangeEnd⟩)) Q) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Auth_AuthEnable_dist`: `(*authClient).AuthEnable(ctx)` across machines** (as
`Auth_UserAdd_dist`, at `irrAuthEnable`). -/
abbrev Auth_AuthEnable_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl ap : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd)
    (Q : List auth.AuthState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      authClientAt cl ap eps V Γ cfg ∗ metadata.outMD ctx om ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗
      histAu γR Γ.kv srvAuthSt0 (fun hm => iprop(⌜userOk (principalOf cfg) hm.username⌝))
        irrAuthEnable Q }}
    (App (Val (ap @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!!
        go!"AuthEnable")) (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ adminRepliedD eps Γ γR (principalOf cfg) irrAuthEnable Q) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-! ### Lease calls, auth on (F2's vocabulary: `view.leaseClientAt`, `Γ.ls mid`, revocable mode; one endpoint) -/

/-- **DRAFT `Lease_GrantOn_dist`: `(*lessor).Grant(ctx, ttl)` at member `mid`, auth on, revocable
mode** (mirrors `client.client_lease_grant_on` at `γl := Γ.ls mid`, in F2's `Lease_GrantLive_dist`
statement: the grant's update persistent at every id (`□ ∀ id`, `writeAuD`), its result `Q m.id σ`; the
member's own check (`requireAuthInfo`'s, `leaseCheckD … True`) at its published index at least the
caller's `n₀`). -/
abbrev Lease_GrantOn_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (A : w64 → auth.AuthNames) (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (L₀ : List EntryModel) (n₀ : Nat)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (ttl : w64)
    (Q : w64 → KVState → IProp GF),
  (∀ a b : w64, A a = A b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  Γ.auth = true → Γ.kv.lm = .revocable → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseUserAt cl lp ep V Γ mid cfg ∗ metadata.outMD ctx om ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      srvReqLogLb γR L₀ ∗ auth.authPubLbM (.on (A mid)) n₀ ∗
      □ (∀ id : w64, writeAuD Γ.kv (principalOf cfg) (.leaseGrant id ttl) L₀ (Q id)) }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ctx))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗ (∃ (i : Nat) (l : Loc),
          lease.leaseLiveFrom (Γ.ls mid) i m.id l ∗ lease.leaseReqIs (Γ.ls mid) m.id ttl) ∗
        (∃ σ : KVState, Q m.id σ) ∗
        ∃ n : Nat, ⌜n₀ ≤ n⌝ ∗ auth.authPubLbM (.on (A mid)) n ∗
          leaseCheckD (A mid) (principalOf cfg) n (fun _ => iprop(True))) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Lease_RevokeOn_dist`: `(*lessor).Revoke(ctx, id)` at member `mid`, auth on** (mirrors
`client.client_lease_revoke_on`: a write through raft, so its update is persistent (`writeAuD`), its
success the result `Q σ` and the grant of `irrLeaseRevoke id` at the history (`writeCheckedD`: the
apply-time `checkLeasePuts`, write permission on every attached key, or an admin), and member `mid`'s
`requireAuthInfo` (`leaseCheckD … True`) at its published index at least `n₀`). -/
abbrev Lease_RevokeOn_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (A : w64 → auth.AuthNames) (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (L₀ : List EntryModel) (n₀ : Nat)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (id : w64)
    (Q : KVState → IProp GF),
  (∀ a b : w64, A a = A b → a = b) →
  Γ.auth = true → Γ.kv.lm = .revocable → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseUserAt cl lp ep V Γ mid cfg ∗ metadata.outMD ctx om ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      srvReqLogLb γR L₀ ∗ auth.authPubLbM (.on (A mid)) n₀ ∗
      writeAuD Γ.kv (principalOf cfg) (.leaseRevoke id) L₀ Q }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Revoke"))
      (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseRevokeRespM, leaseRevokeRespMsg resp m ∗
        (∃ σ : KVState, Q σ) ∗
        writeCheckedD [ep] Γ γR (principalOf cfg) (irrLeaseRevoke id) L₀ ∗
        ∃ n : Nat, ⌜n₀ ≤ n⌝ ∗ auth.authPubLbM (.on (A mid)) n ∗
          leaseCheckD (A mid) (principalOf cfg) n (fun _ => iprop(True))) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Lease_TimeToLiveKeysOn_dist`: `(*lessor).TimeToLive(ctx, id, WithAttachedKeys())` at member
`mid`, auth on** (F2's `Lease_TimeToLiveKeys_dist` row; mirrors `lessor.TimeToLive.spec` at
`etcdLeaseTTLSpecMdW` with `leaseKeysFold gs false = true`: `checkLeaseTimeToLive` runs at the member that
received the call, over its own auth store and its own lessor (`s.lessor.Lookup`), before the TTL itself
is asked of the leader. So the success is the echoed `ID` (F2's view-free claim: nothing of the TTL, which
the leader answers) and member `mid`'s keys verdict (`leaseKeysVerdictFrom`: the lease absent, or each
attached key readable) at its published auth index `n ≥ n₀` and its lessor's index `j ≥ m₀`; or the
member's admin pass). -/
abbrev Lease_TimeToLiveKeysOn_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (A : w64 → auth.AuthNames) (cfg : go_etcd_io.etcd.client.v3.Config) (n₀ m₀ : Nat)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (id : w64)
    (sl : GoSlice) (gs : List (Bool → Bool)),
  (∀ a b : w64, A a = A b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  Γ.auth = true → outTokOk (principalOf cfg) om → leaseKeysFold gs false = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseUserAt cl lp ep V Γ mid cfg ∗ metadata.outMD ctx om ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      leaseOptsAt sl gs ∗ auth.authPubLbM (.on (A mid)) n₀ ∗ lease.lessorLb (Γ.ls mid) m₀ }}
    (App (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!!
        go!"TimeToLive")) (Val #(GoInterface.ok ctx))) (Val #id)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗
          structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"ID" resp ↦□ id ∗
          ∃ n j : Nat, ⌜n₀ ≤ n ∧ m₀ ≤ j⌝ ∗ auth.authPubLbM (.on (A mid)) n ∗ lease.lessorLb (Γ.ls mid) j ∗
            leaseCheckD (A mid) (principalOf cfg) n
              (fun info => leaseKeysVerdictFrom (.on (A mid)) n info (Γ.ls mid) j id .read)) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Lease_LeasesOn_dist`: `(*lessor).Leases(ctx)` at member `mid`, auth on, revocable mode**
(F2's `Lease_LeasesLive_dist` statement, with `checkLeaseLeases`' verdict: member `mid`'s own lessor
listing at an index `j ≥ m₀`, and its check at its published auth index `n ≥ n₀`: an admin, or every
listed lease's attached keys readable (`leaseKeysVerdictFrom` at `j`)). -/
abbrev Lease_LeasesOn_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (A : w64 → auth.AuthNames) (cfg : go_etcd_io.etcd.client.v3.Config) (n₀ m₀ : Nat)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (om : GrpcMd),
  (∀ a b : w64, A a = A b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  Γ.auth = true → Γ.kv.lm = .revocable → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseUserAt cl lp ep V Γ mid cfg ∗ metadata.outMD ctx om ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      auth.authPubLbM (.on (A mid)) n₀ ∗ lease.lessorLb (Γ.ls mid) m₀ }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice) (j n : Nat),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗
          ⌜m₀ ≤ j ∧ n₀ ≤ n⌝ ∗ lease.leaseIdsAt (Γ.ls mid) j ids ∗ auth.authPubLbM (.on (A mid)) n ∗
          leaseCheckD (A mid) (principalOf cfg) n
            (fun info => iprop([∗list] id ∈ ids,
              leaseKeysVerdictFrom (.on (A mid)) n info (Γ.ls mid) j id .read))) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
