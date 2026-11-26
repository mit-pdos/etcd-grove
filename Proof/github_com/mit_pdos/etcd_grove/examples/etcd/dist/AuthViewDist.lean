/-
**DRAFTS of the auth-on interim contracts at the cluster view** (F7, `notes/etcd-dist-f7.md`; #50, 2026-11-26).
Lean-first (no Rocq counterpart).

STATEMENTS ONLY: definitions, no axiom, no proof, no `sorry`. Nothing imports this file. Each draft
`X.spec` becomes `axiom X.wp_proof : X.spec` in its own Spec/Proof pair beside `KVPutDist.lean` only after
a fresh `axiom`-skill review, and joins the etcd_safe packet (`notes/etcd-dist-f7.md`, "The axioms").

The vocabulary (see the note, "The view"):
* the cluster's auth history is `Γ.kv.hist` (one name for every member: `etcdstart.memberGOkOn`), and the
  requested log `Γ.kv.rlog` (`srvReqLogLb γR L` at any `γR` with `γR.raft.log = Γ.kv.rlog`, the one field
  it reads);
* `A : w64 → auth.AuthNames`, member `mid`'s auth names (joins `DistView` as `au` at implementation, with
  the Prove item P-A1, `NewServer` taking `γa` from the start as P-L1 takes the lessor's); only the member-local
  reads read it (the published index, `auth.authPubLbM`);
* a call's principal is the client's configured user name (`principalOf cfg`, from `New`'s `cfg` field),
  never a token: a token is a member's (the simple provider's), the contracts say only which user a
  granted request was bound to (`userOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Spec.go_etcd_io.etcd.client.v3.New
public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn

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
client (empty user name or password: `New` then authenticates nothing, `clientAuthPre_anon`). -/
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
cluster's KV names, told the grant (`opGrantD`) at a lower bound `L₀` of the requested log the caller
holds. -/
def writeAuD (γR : ServerRaftNames) (γk : KVNames) (P : Option GoString) (op : KVOp)
    (Q : KVState → IProp GF) : IProp GF :=
  iprop(∃ L₀ : List EntryModel, srvReqLogLb γR L₀ ∗
    □ kvAu1G γk (kvOpStep op) (opGrantD γk P op L₀) Q)

/-- **What an admin call's success tells the caller** (`v3rpc.adminReplied` at the cluster: the member's
publication `pubAfterM` and the token binding dropped, the requested log in place of the committed one):
the stamped request, admitted and applied after the requested prefix `L` (`adminDoneM`), its result
(`adminQh`: the history update's `Q`), its header's user one `P` may be bound to. -/
def adminRepliedD (γR : ServerRaftNames) (γk : KVNames) (P : Option GoString) (rq : apply.IRRModel)
    (Q : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (L : List EntryModel),
    ⌜irrWireOf (apply.withHeader rq hm) rq' ∧ adminDoneM true γk rq' L ∧ userOk P hm.username⌝ ∗
    srvReqLogLb γR L ∗ adminQh γk rq Q hm L)

/-- **What a successful auth-on read tells the caller of its check**: the principal it was bound to
read `[key, end)` at the auth state after a requested prefix `L` extending `L₀` (for a linearizable read,
at or after its read index; for a serializable one, the member's published state: `A mid`'s index at
least `n`). -/
def readAuthedD (γk : KVNames) (P : Option GoString) (L₀ : List EntryModel) (o : OpFull) : Prop :=
  ∃ (user e : GoString) (rv : Nat) (L : List EntryModel), userOk P user ∧ L₀ <+: L ∧
    apply.authEndOf o.base.rangeEnd e ∧
    auth.permitted (srvAuthAtLog γk srvAuthSt0 L) ⟨user, rv⟩ o.key e .read

/-- **What every auth-on contract takes of the client**: `kvClientAt`'s (its `KV` the `*kv` `api`), and
its configuration `cfg`, read-only (whose user name is the principal). -/
def userClientAt [NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) : IProp GF :=
  iprop(kvClientAt cl api eps V Γ ∗ clientF cl go!"cfg" ↦□ cfg)

/-- **An auth client of the view**: `New`'s client of endpoints serving `Γ`, with no proxy, its `Auth`
field the `*authClient` `ap`, its configuration `cfg`. -/
def authClientAt [NetProtoGS] (cl ap : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) : IProp GF :=
  iprop(isNewClient cl eps V ∗ clientNoProxy cl ∗ clientF cl go!"cfg" ↦□ cfg ∗
    clientF cl go!"Auth" ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty) #ap : GoInterface) ∗
    membersAt (Gg := hG.goose_globalGS) eps Γ)

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

/-- **DRAFT `New_user_dist`: `clientv3.New(cfg)` with a user name, across machines** (mirrors
`clientv3.New.spec`, whose `clientAuthPre` registration of `Authenticate` at `eps` is replaced by the
address facts of an auth-on view; `clientTokAt` dropped from the post: the tokens are the members', the
auth-on contracts read the principal from `cfg`). `New` calls `Auth.Authenticate` at an endpoint when it
dials (`getToken`); a wrong password or an auth-off member is the error arm. -/
abbrev New_user_dist.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] [NetProtoGS] (cfg : go_etcd_io.etcd.client.v3.Config)
    (eps : List GoString) (V : WEnv GF) (Γ : DistView),
  Γ.auth = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ levelTok 0 ∗
      clientCfgOk cfg eps ∗ ⌜strsSizeOk [cfg.Username', cfg.Password']⌝ ∗
      membersAt (Gg := hG.goose_globalGS) eps Γ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.New)) (Val #cfg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ isNewClient cl eps V ∗ clientF cl go!"cfg" ↦□ cfg) ∨
        ⌜err ≠ GoInterface.nil ∧ cl = null⌝) }}

/-- **DRAFT `KV_PutOn_dist`: `(*kv).Put(ctx, key, val, opts...)` across machines, auth on** (mirrors
`client.client_put_on` at the cluster: `etcdPutSpecOn`'s registration replaced by `kvClientAt` at `Γ`, the
member's floor `F` dropped, the update persistent (`writeAuD`: a write is resent after
`ErrInvalidAuthToken`'s token refresh, `isSafeRetryMutableRPC` does not apply), the token's binding replaced
by the principal of `cfg`; the error arm claims nothing). A lease `0`, or the revocable lease mode, as
`etcdPutSpecOn`'s filter. -/
abbrev KV_PutOn_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (key val : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      userClientAt cl api eps V Γ cfg ∗ metadata.outMD ctx om ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ (opPutModel key val opts).putPanics ∧ (opPutModel key val opts).t = W64 2 ∧
        ((putWireOf (opPutModel key val opts)).leaseID = W64 0 ∨ Γ.kv.lm = .revocable)⌝ ∗
      writeAuD γR Γ.kv (principalOf cfg) (.put (putWireOf (opPutModel key val opts))) Q ∗
      ⌜opSizeOk (opPutModel key val opts)⌝ }}
    (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #val)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
        ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ kvRevFits (σ.rev + 1) ∧ kvLogOk σ⌝ ∗
        kvRevLb Γ.kv m.hdr.revision) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `KV_GetOn_dist`: `(*kv).Get(ctx, key, opts...)` across machines, auth on** (`KV_Get_dist`'s
statement, for an auth-on view, at the principal of `cfg`, and a success also tells the read's check
(`readAuthedD`) above the caller's lower bound `L₀` of the requested log: a linearizable read's check is no
older than its read index, which is at least every commit before the call). Serializable reads are not
covered (no workload sends one with auth on): `serializable = false` is a premise. -/
abbrev KV_GetOn_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF),
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
            m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev ∧ kvLogOk σ ∧
            readAuthedD Γ.kv (principalOf cfg) L₀ (rangeWireOf (opGetModel key opts))⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝)) }}

/-- **DRAFT `Auth_UserAdd_dist`: `(*authClient).UserAdd(ctx, name, pw)` across machines** (mirrors
`authClient.UserAdd.spec` at `etcdUserAddSpecW`: the caller's persistent history update `histAu` at the
cluster's names, the binding `userOk` of `cfg`'s principal; a success the cluster-level `adminRepliedD`).
Sent by the set-up's anonymous client before `AuthEnable`; stated for either auth mode of the history. -/
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
          adminRepliedD γR Γ.kv (principalOf cfg) (irrUserAdd um) Q) ∨
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
      ((⌜err = GoInterface.nil⌝ ∗ adminRepliedD γR Γ.kv (principalOf cfg) irrAuthEnable Q) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
