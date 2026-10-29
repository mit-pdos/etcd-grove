/-
`SetUp(cli)` (`examples/authkv/authkv.go`; the auth plan's E2h). Lean-first (no Rocq
counterpart).

`SetUp` puts the keys the principals' deletes may remove (`setupKeys`: `x/<who>/d` for every
principal `who` and `x` in `a`, `c`), each in a context with the examples' request timeout, then,
in one such context, makes the eight admin calls that create the auth state and enable auth
(`setupCalls`: user `root` with role `root`, role `r` granted `READWRITE` on `[a, b)`, user `u`
with role `r`, user `v`, `AuthEnable`), returning `false` at the first that fails.

What the server's Auth service guarantees is a premise in the client's terms (`notes/decisions.md`,
"E2h of the auth plan"): for each admin method its spec (`isGrpcRpc` at the endpoint, a
`GrpcSpec` over the request's wire model) and, for each call, the caller's persistent
`□ ▷ Spec m (fun _ => Q)`: what the client may ask of a request the retry interceptor can deliver
several times. When `SetUp` returns `true`, every call returned `nil`, so each call's `Q` holds;
the server's side (the apply layer's admin steps, `apply.isAuthSteps`, behind the Auth service's
handlers) chooses the `Q`s (the step applied to the auth history, its revision) when it
discharges the premise.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Checks
public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI

/-- The keys `SetUp` puts, in order: `x/<who>/d` for every principal and `x` in `a`, `c`. -/
def setupKeys : List GoString :=
  principals.flatMap fun w => keyParts.map fun x => keyOfK x w go!"d"

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- **The Auth service at `ep` for `SetUp`'s admin calls** (persistent; the premise the server's
side discharges): the specs of the five admin methods at the endpoint, and each call's
persistent precondition with its `Q`. -/
def setupAuthOk (ep : GoString)
    (Su : GrpcSpec (GF := GF) pbAuthUserAddRequest pbAuthUserAddResponse)
    (Sg : GrpcSpec (GF := GF) pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse)
    (Sr : GrpcSpec (GF := GF) pbAuthRoleAddRequest pbAuthRoleAddResponse)
    (Sp : GrpcSpec (GF := GF) pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse)
    (Se : GrpcSpec (GF := GF) pbAuthEnableRequest pbAuthEnableResponse)
    (Q : Fin 8 → IProp GF) : IProp GF :=
  iprop(isGrpcRpc ep go!"/etcdserverpb.Auth/UserAdd" Su ∗
    isGrpcRpc ep go!"/etcdserverpb.Auth/UserGrantRole" Sg ∗
    isGrpcRpc ep go!"/etcdserverpb.Auth/RoleAdd" Sr ∗
    isGrpcRpc ep go!"/etcdserverpb.Auth/RoleGrantPermission" Sp ∗
    isGrpcRpc ep go!"/etcdserverpb.Auth/AuthEnable" Se ∗
    □ ▷ Su ⟨go!"root", go!"root-pw"⟩ (fun _ => Q 0) ∗
    □ ▷ Sg (go!"root", go!"root") (fun _ => Q 1) ∗
    □ ▷ Sr go!"r" (fun _ => Q 2) ∗
    □ ▷ Sp (go!"r", ⟨W32 2, go!"a", go!"b"⟩) (fun _ => Q 3) ∗
    □ ▷ Su ⟨go!"u", go!"u-pw"⟩ (fun _ => Q 4) ∗
    □ ▷ Sg (go!"u", go!"r") (fun _ => Q 5) ∗
    □ ▷ Su ⟨go!"v", go!"v-pw"⟩ (fun _ => Q 6) ∗
    □ ▷ Se () (fun _ => Q 7))

instance setupAuthOk_persistent (ep : GoString) Su Sg Sr Sp Se (Q : Fin 8 → IProp GF) :
    Persistent (setupAuthOk ep Su Sg Sr Sp Se Q) := by
  unfold setupAuthOk; infer_instance

/-- See the file header. `New`'s client `cl` of the member at `ep` (`isNewClient`), its `KV` a
`*kv` over its connection (`clientTokAt`, at any `P`: the set-up's client has no user name), the
member's `Put` registered with etcd's spec with auth on (`etcdPutSpecOn`, what an auth-on member's
`etcd_kv_auth_served_on` gives; S5 of `notes/authkv-main-plan.md`: until 2026-10-29 the plain
`kvRegsAt`, which an auth-on member does not give), with the caller's update for each set-up put
(`kvOpAu1`, persistent: the put may be delivered several times) and the Auth service's premise
`setupAuthOk`: `SetUp` returns some revision and `ok`, and if `ok` every admin call's `Q`. -/
abbrev SetUp.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ep : GoString) (V : client.WEnv GF) (P : GoString → IProp GF) (s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (Su : GrpcSpec (GF := GF) pbAuthUserAddRequest pbAuthUserAddResponse)
    (Sg : GrpcSpec (GF := GF) pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse)
    (Sr : GrpcSpec (GF := GF) pbAuthRoleAddRequest pbAuthRoleAddResponse)
    (Sp : GrpcSpec (GF := GF) pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse)
    (Se : GrpcSpec (GF := GF) pbAuthEnableRequest pbAuthEnableResponse) (Q : Fin 8 → IProp GF),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      isNewClient cl [ep] V ∗ clientTokAt cl [ep] P ∗
      isGrpcRpcMd ep go!"/etcdserverpb.KV/Put" (client.etcdPutSpecOn s E ρ cid mid) ∗
      iprop(□ ∀ k : GoString, ⌜k ∈ setupKeys⌝ -∗
        kvOpAu1 ρ.rd.kv (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True))) ∗
      setupAuthOk ep Su Sg Sr Sp Se Q }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.SetUp)) (Val #cl))
  {{ (rev : w64) (ok : Bool), RET (PairV #rev #ok);
      if ok then iprop(Q 0 ∗ Q 1 ∗ Q 2 ∗ Q 3 ∗ Q 4 ∗ Q 5 ∗ Q 6 ∗ Q 7) else iprop(True) }}

end spec

end authkv
end EtcdGrove
end Perennial
