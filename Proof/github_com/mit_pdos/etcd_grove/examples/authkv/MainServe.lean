/-
**etcd's server, started for authkv** (2026-10-30). Lean-first (no Rocq counterpart).

`ak_served_kv`: the ghost step between `net.Listen` and `go gs.Serve(l)` with auth on, watchkv's
`wk_served` without the watch: from `v3rpc.Server`'s postcondition (`grpcUpOn`), the member's
started facts (`memberUpOn`'s `srvBcryptField`), the listener and the run slots, the right to serve,
etcd's KV methods with auth on at the address (`akKVOn`), the five Auth admin methods
(`setupAuthServed`) and `Authenticate` (`etcd_kv_auth_served_onA`). The watch half waits on the
mode-generic `srvKVFacts` (`notes/authkv-main-plan.md`, "Main: what blocks it", item 1).

`bcryptCostOk_of_field`: the auth store's `BcryptCost()` returns, from its read-only field
(`authStore.BcryptCost.spec`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.AuthnServedOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__BcryptCost
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.WorkEnv
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.SetUp

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [es_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **The auth store's `BcryptCost()` returns**, from its read-only `bcryptCost` field. -/
theorem bcryptCostOk_of_field (wp : auth.authStore.BcryptCost.spec (GF := GF)) (stl : Loc)
    (c : w64) :
    structFieldRef go_etcd_io.etcd.server.v3.auth.authStore go!"bcryptCost" stl ↦□ c ⊢
      bcryptCostOk (GF := GF)
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty, #stl⟩ := by
  iintro #Hc
  unfold bcryptCostOk
  iintro !> %Φ !> - HΦ
  iapply (wp stl c) $$ [Hc]
  · iexact Hc
  iintro !> -
  iapply HΦ
  itrivial

/-- **etcd's server, started for authkv: its KV and Auth services** (see the file header). -/
theorem ak_served_kv (addr : GoString) (gs q p pa s : Loc) (lis : GoInterface)
    (E : apply.AEnv GF) (ρ : ReqNames) (cid mid n : w64) (il im iu ims is : GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × val × GoInterface)) (N : Nat)
    (γa : auth.AuthNames) (hγa : E.authMode = .on γa)
    (hregs : ∀ x ∈ v3rpc.kvRegs q, x ∈ regs) (hregsA : ∀ x ∈ v3rpc.authRegs pa, x ∈ regs)
    (wpBC : auth.authStore.BcryptCost.spec (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E ρ.rd ∗ srvAuthLb s E ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ ρ.rd (W64 0) [] .none 0 none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        v3rpc.authServerIs pa s ∗ srvBcryptField s ∗
        (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk il (srvLgReader s) Q) ∗
        (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk im iprop(True) Q) ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcSrvNew gs [il, im, iu] [ims, is] svcs regs sregs ∗ netListenerAt lis addr ∗
        ([∗list] _x ∈ List.replicate N (), client.etcdGrpcSlot s E ρ.rd) ⊢
      |={⊤}=> grpcServeTok gs lis ∗ grpcStreamServerAt addr [ims, is] sregs ∗
        akKVOn addr s E ρ cid mid ∗ setupAuthServed addr s E ρ ∗
        isGrpcRpc addr authnMethod (client.etcdAuthenticateSpec γa) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hlb, #Hat, #HNR, #Hq, #Hpa, #HBF, #Hil, #Him, #Hiu, Hgs,
    Hlis, Hslots⟩
  imod (grpc.start gs lis addr [il, im, iu] [ims, is] svcs regs sregs) $$ [Hgs Hlis]
    with ⟨Hat', Hss, Htok⟩
  · iframe
  iunfold srvBcryptField at HBF
  icases HBF with ⟨%stl, %c, #Hfld, #Hc⟩
  ihave #Hbc := bcryptCostOk_of_field wpBC stl c $$ Hc
  ihave #Hil' := Hil $$ %v3rpc.learnerReqOk
  ihave #Him' := Him $$ %v3rpc.learnerReqOk
  imod (client.etcd_kv_auth_served_onA addr p q pa s E ρ ρ.rd cid mid n il im iu
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty, #stl⟩ regs N γa hγa
      (by
        intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hregs x h
        · exact hregsA x h)) $$ [Hat' Hslots]
    with ⟨#Hput, #Hrange, #Hdel, #Htxn, #Hua, #Hug, #Hra, #Hrg, #Hae, #Hauth⟩
  · iframe; iframe #
  imodintro
  iframe Htok Hss Hauth
  isplitl []
  · unfold akKVOn
    iframe #
  unfold setupAuthServed
  iframe #

end served

end authkv
end EtcdGrove
end Perennial
