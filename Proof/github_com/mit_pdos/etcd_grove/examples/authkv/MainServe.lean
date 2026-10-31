/-
**etcd's server, started for authkv** (2026-10-30). Lean-first (no Rocq counterpart).

`ak_served_kv`: the ghost step between `net.Listen` and `go gs.Serve(l)` with auth on, watchkv's
`wk_served` without the watch: from `v3rpc.Server`'s postcondition (`grpcUpOn`), the member's
started facts (`memberUpOn`'s `srvAuthStoreOn`: the store's cost field and `Authenticate` side), the listener and the run slots, the right to serve,
etcd's KV methods with auth on at the address (`akKVOn`), the five Auth admin methods
(`setupAuthServed`) and `Authenticate` (`etcd_kv_auth_served_on`). `ak_served_watch`: its watch
half, from the stream server `ak_served_kv` returns, the watch server and its run slots: the watch
server's facts at the address (`watchAddrFacts`) and its mode (`modeTag`, `Work`'s), the members' KV facts from the auth-on read view
(`srvKVCoreM_of_readM`, G2's mode-generic `srvKVFacts`).

`bcryptCostOk_of_field`: the auth store's `BcryptCost()` returns, from its read-only field
(`authStore.BcryptCost.spec`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.AuthnServedOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__BcryptCost
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.WorkEnv
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.SetUp
public import Proof.go_etcd_io.etcd.client.v3.WatchLawsHist
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart

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

/-- **etcd's server, started for authkv: its KV and Auth services** (see the file header); under
`grpcRepliesFit`, which it gives `grpc.start`. -/
theorem ak_served_kv (addr : GoString) (gs q p pa s : Loc) (lis : GoInterface)
    (E : apply.AEnv GF) (ρ : ReqNames) (cid mid n : w64) (il im iu ims is : GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × val × GoInterface)) (N : Nat)
    (γa : auth.AuthNames) (hγa : E.authMode = .on γa)
    (hregs : ∀ x ∈ v3rpc.kvRegs q, x ∈ regs) (hregsA : ∀ x ∈ v3rpc.authRegs pa, x ∈ regs)
    (wpBC : auth.authStore.BcryptCost.spec (GF := GF)) (Hrf : grpcRepliesFit) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E ρ.rd ∗ srvAuthLb s E ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ ρ.rd (W64 0) [] .none 0 none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        v3rpc.authServerIs pa s ∗ srvAuthStoreOn s E.RD ∗
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
  imod (grpc.start gs lis addr [il, im, iu] [ims, is] svcs regs sregs Hrf) $$ [Hgs Hlis]
    with ⟨Hat', Hss, Htok⟩
  · iframe
  iunfold srvAuthStoreOn at HBF
  icases HBF with ⟨%stl, %c, #Hfld, #Hc, #Hau⟩
  ihave #Hbc := bcryptCostOk_of_field wpBC stl c $$ Hc
  ihave #Hil' := Hil $$ %v3rpc.learnerReqOk
  ihave #Him' := Him $$ %v3rpc.learnerReqOk
  imod (client.etcd_kv_auth_served_on addr p q pa s E ρ ρ.rd cid mid n il im iu
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


/-- **etcd's server, started for authkv: its watch service** (see the file header): watchkv's
`wk_served`'s watch half, with the members' KV facts from the read view with auth on. -/
theorem ak_served_watch [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (V : client.WEnv GF) (addr : GoString) (pw s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (ims is : GoFunc) (sregs : List (GoString × val × GoInterface)) (nw : Nat)
    (hV : V.addr = addr) (hE : V.R.E = E) (hp : V.pfx ≠ []) (hst : γr.kv.st = V.kst)
    (hlog : γr.kv.log0 = [[], []]) (hrb : receiptBound GF ≤ 2 ^ 62)
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      go_etcd_io.etcd.api.v3.etcdserverpb.WatchServer.ty = true)
    (hwreg : (go!"/etcdserverpb.Watch/Watch",
      (@! go_etcd_io.etcd.api.v3.etcdserverpb._Watch_Watch_Handler : val),
      interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #pw) ∈ sregs)
    (hWM : V.WM = v3rpc.etcdModelOfServer V.R.E) (hWL : V.WL = client.srvWL V.R)
    (hoff : V.R.E.γ.cm = false) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isServerReadM true s E γr ∗ v3rpc.isWatchServer pw V.R ∗
        srvStreamInterceptorOk ims iprop(True) ∗ srvStreamInterceptorOk is iprop(True) ∗
        grpcStreamServerAt addr [ims, is] sregs ∗
        ([∗list] _x ∈ List.replicate nw (), v3rpc.watchRunSlot V.R) ∗ client.eofOk ⊢
      |={⊤}=> watchAddrFacts V ∗ auth.modeTag V.R.γ.tag E.authMode := by
  iintro ⟨#Ppb, #Pv, #Hrd, #Hws, #Hims, #His, Hss, Hwslots, #Heof⟩
  ihave #Htag : auth.modeTag V.R.γ.tag E.authMode $$ []
  · iunfold v3rpc.isWatchServer at Hws
    icases Hws with ⟨-, -, -, -, -, -, -, -, #Hok⟩
    iunfold v3rpc.watchSrvOk at Hok
    icases Hok with ⟨-, -, -, -, -, -, #Ht, -⟩
    rw [← hE]; iexact Ht
  imod (v3rpc.etcd_watch_served_chain addr pw V.R ims is sregs nw hset hwreg) $$ [Hss Hwslots]
    with #Hst
  · iframe; iframe #
  ihave ⟨%Hlink, #H0⟩ := client.isWatchServer_start pw V.R $$ Hws
  ihave #Htok := client.watchTokPool_of_server pw V.R $$ Hws
  ihave #Hsm := client.srvLogsSmall_of_receipts V.R Hlink hrb
  ihave #Hnc := v3rpc.isWatchServer_noCompactor_env pw V.R hoff $$ Hws
  ihave #Hcore := srvKVCoreM_of_readM true s E γr $$ Hrd
  ihave #Hkf := client.srvKVFacts_intro V true γr hst hlog hrb $$ [Hcore H0]
  · rw [← Hlink, hE]; iframe #
  ihave #Hlaws := client.watchLaws_srv V hWM hWL Hlink $$ Hkf
  imodintro
  iframe Htag
  unfold watchAddrFacts
  rw [hV]
  iframe #
  ipureintro; exact ⟨Hlink, hp⟩

end served

end authkv
end EtcdGrove
end Perennial
