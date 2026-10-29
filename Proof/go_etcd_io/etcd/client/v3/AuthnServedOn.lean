/-
**etcd's server serves `Authenticate` with auth on** (the auth plan's C1, layer 4, 2026-10-28;
`notes/c1-plan.md`): the spec it registers for `Auth.Authenticate` (`etcdAuthenticateSpec`: a
reply's token is issued to the user named, `auth.tokIssued`), and what a client's `New` takes of it
(`authTokReg_of`: `clientAuthPre`'s registration at the tokens issued to the user). Lean-first (no
Rocq counterpart).

Phase 1 of the spec-first stage: `etcd_kv_auth_served_onA` is `etcd_kv_auth_served_on` with
`Authenticate` served too, a `sorry` until the handler's proof (S5's `authStore.Authenticate`
through `EtcdServer.Authenticate`, which has no spec yet, and `AuthServer.Authenticate`); it then
replaces `etcd_kv_auth_served_on`. It is stated apart so that the latter's users do not rest on the
`sorry` meanwhile.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ServedOn
public import Proof.go_etcd_io.etcd.client.v3.ClientUser

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **etcd's spec of `Auth.Authenticate` with auth on, at the member's names `γa`**: a reply's
token is issued to the user named in the request (`auth.tokIssued`). The password and the
request's size ask nothing of the client: a wrong password, or a request too large, is an error. -/
def etcdAuthenticateSpec (γa : auth.AuthNames) :
    GrpcSpec (GF := GF) pbAuthenticateRequest pbAuthenticateResponse :=
  fun (m : GoString × GoString) (Φ : GoString → IProp GF) =>
    iprop(∀ t, auth.tokIssued γa t m.1 -∗ Φ t)

/-- `New`'s registration (`authTokReg`) for the user `u`, at the tokens issued to `u`, from the
member's `Authenticate` with auth on. -/
theorem authTokReg_of (addr u pw : GoString) (γa : auth.AuthNames) :
    isGrpcRpc (GF := GF) addr authnMethod (etcdAuthenticateSpec γa) ⊢
      authTokReg [addr] u pw (fun t => auth.tokIssued γa t u) := by
  iintro #H
  unfold authTokReg
  iexists etcdAuthenticateSpec γa
  isplitl []
  · iapply (isGrpcRpcs_singleton _ _ _).1
    iexact H
  · iintro !> !>
    unfold etcdAuthenticateSpec
    iintro %t #Ht !>
    iexact Ht

/-- **`etcd_kv_auth_served_on` with `Authenticate` served too** (see the file header; `sorry`
until the handler's proof). -/
theorem etcd_kv_auth_served_onA (addr : GoString) (p q pa s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64) (il im iu : GoFunc)
    (ast : GoInterfaceOk) (regs : List (GoString × val × GoInterface)) (N : Nat)
    (γa : auth.AuthNames) (hγa : E.authMode = .on γa)
    (hregs : ∀ x ∈ etcdKVRegs (GF := GF) q ++ v3rpc.authRegs pa, x ∈ regs)
    (hreg : (authnMethod, (@! etcdserverpb._Auth_Authenticate_Handler),
      interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #pa) ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        v3rpc.authServerIs pa s ∗
        structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗ bcryptCostOk ast ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcServerAt addr [il, im, iu] regs ∗
        ([∗list] _x ∈ List.replicate N (), etcdGrpcSlot s E γr) ⊢
      |={⊤}=> isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn s E ρ cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn s E γr cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpecOn s E ρ cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpecOn s E ρ γr cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/UserAdd" (v3rpc.etcdUserAddSpec s E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/UserGrantRole" (v3rpc.etcdUserGrantRoleSpec s E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/RoleAdd" (v3rpc.etcdRoleAddSpec s E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/RoleGrantPermission"
          (v3rpc.etcdRoleGrantPermissionSpec s E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/AuthEnable" (v3rpc.etcdAuthEnableSpec s E ρ) ∗
        isGrpcRpc addr authnMethod (etcdAuthenticateSpec γa) := by
  sorry

end proofs

end client
end EtcdGrove
end Perennial
