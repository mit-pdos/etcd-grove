/-
`SetUp(cli)` (`examples/authkv/authkv.go`; the auth plan's E2h). Lean-first (no Rocq
counterpart).

`SetUp` puts the keys the principals' deletes may remove (`setupKeys`: `x/<who>/d` for every
principal `who` and `x` in `a`, `c`), each in a context with the examples' request timeout, then,
in one such context, makes the eight admin calls that create the auth state and enable auth
(`setupCalls`: user `root` with role `root`, role `r` granted `READWRITE` on `[a, b)`, user `u`
with role `r`, user `v`, `AuthEnable`), returning `false` at the first that fails.

The admin calls go to etcd's Auth service at `ep` (`setupAuthServed`: the five methods' specs, what
an auth-on member serves), through a client with no user (`clientTokAt cl [ep] (fun _ => False)`:
no attempt carries a credential token) and a server with no TLS identity, so the history's updates
are `SetUp`'s alone: it holds the client's view of the auth history (`authHistView`, at the boot
history). When `SetUp` returns `true`, the history is frozen (`authHistFrozen`: no admin request
changes the auth state after it, the auth-mode merge's 5b) at a log `Lset` whose auth state is
`setupSt r`, published (`authPubLb`, `authStateAt`); when it returns `false`, nothing (`Main`
stops).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Checks
public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- **etcd's Auth service at `ep`, for `SetUp`'s admin calls** (persistent): the five admin
methods registered with etcd's specs (`v3rpc.etcd*Spec`, what an auth-on member's
`etcd_kv_auth_served_on` gives). -/
def setupAuthServed (ep : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(isGrpcRpcMd ep go!"/etcdserverpb.Auth/UserAdd" (v3rpc.etcdUserAddSpec s E ρ) ∗
    isGrpcRpcMd ep go!"/etcdserverpb.Auth/UserGrantRole" (v3rpc.etcdUserGrantRoleSpec s E ρ) ∗
    isGrpcRpcMd ep go!"/etcdserverpb.Auth/RoleAdd" (v3rpc.etcdRoleAddSpec s E ρ) ∗
    isGrpcRpcMd ep go!"/etcdserverpb.Auth/RoleGrantPermission"
      (v3rpc.etcdRoleGrantPermissionSpec s E ρ) ∗
    isGrpcRpcMd ep go!"/etcdserverpb.Auth/AuthEnable" (v3rpc.etcdAuthEnableSpec s E ρ))

instance setupAuthServed_persistent (ep : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    Persistent (setupAuthServed ep s E ρ) := by
  unfold setupAuthServed; infer_instance

/-- See the file header. `New`'s client `cl` of the member at `ep` (`isNewClient`), its `KV` and
`Auth` over one connection whose attempts carry no credential token (`clientTokAt` at
`fun _ => False`), the member's `Put` registered with etcd's spec with auth on (`etcdPutSpecOn`;
S5 of `notes/authkv-main-plan.md`), with the caller's update for each set-up put (`kvOpAu1`,
persistent: the put may be delivered several times), the member's Auth service
(`setupAuthServed`), its server `s` with no TLS identity (`ClientCertAuthEnabled` false at boot),
and the client's view of the auth history at the boot history; the member in the auth mode `on`
at `γa`, its consistent index at start at most its start index (as at boot, where it is `0`). -/
abbrev SetUp.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ep : GoString) (V : client.WEnv GF) (s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) (γa : auth.AuthNames),
  E.authMode = .on γa →
  uint.Z ρ.kv.c0 ≤ uint.Z ρ.raft.ai0 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      isNewClient cl [ep] V ∗ clientTokAt cl [ep] (fun _ => iprop(False)) ∗
      isGrpcRpcMd ep go!"/etcdserverpb.KV/Put" (client.etcdPutSpecOn s E ρ cid mid) ∗
      iprop(□ ∀ k : GoString, ⌜k ∈ setupKeys⌝ -∗
        kvOpAu1 ρ.rd.kv (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True))) ∗
      setupAuthServed ep s E ρ ∗ □ (srvTLSId s -∗ False) ∗
      authHistView ρ.kv [srvAuthSt0] }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.SetUp)) (Val #cl))
  {{ (rev : w64) (ok : Bool), RET (PairV #rev #ok);
      if ok then
        iprop(∃ (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel) (k : Nat)
            (r : Nat),
          authHistFrozen ρ.kv γz hs ∗ srvReqLogLb ρ.raft Lset ∗
          ⌜admStates ρ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog ρ.kv srvAuthSt0 Lset = setupSt r⌝ ∗
          auth.authPubLb γa k ∗ auth.authStateAt γa k (setupSt r))
      else iprop(True) }}

end spec

end authkv
end EtcdGrove
end Perennial
