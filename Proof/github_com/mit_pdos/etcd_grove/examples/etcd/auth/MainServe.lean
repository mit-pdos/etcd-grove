/-
**etcd's server, started for authkv** (2026-10-30). Lean-first (no Rocq counterpart).

`ak_served_kv`: the ghost step between `net.Listen` and `go gs.Serve(l)` with auth on, watchkv's
`etcd_watch.wk_served_nd` without the watch: from `v3rpc.Server`'s postcondition (`grpcUpOn`), the member's
started facts (`memberUpOn`'s `srvAuthStoreOn`: the store's cost field and `Authenticate` side), the listener and the run pools, the right to serve,
etcd's KV methods with auth on at the address (`akKVOn`), the five Auth admin methods
(`setupAuthServed`) and `Authenticate` (`etcd_kv_auth_served_on`), and the persistent server token
(`grpcServerAt`, for further registrations: auth-lease S4's Lease service). `ak_served_watch`: its watch
half, from the stream registration `ak_served_kv` returns (SW1: the start registers the stream) and the watch server: the watch
server's facts at the address (`watchAddrFacts`) and its mode (`modeTag`, `Work`'s), the members' KV facts from the auth-on read view
(`srvKVCoreM_of_readM`, G2's mode-generic `srvKVFacts`).

`bcryptCostOk_of_field`: the auth store's `BcryptCost()` returns, from its read-only field
(`authStore.BcryptCost.spec`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.AuthnServedOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__BcryptCost
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkEnv
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.SetUp
public import Proof.go_etcd_io.etcd.client.v3.WatchLawsHist
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [es_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
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
`grpcRepliesFit`, which it gives `grpc.start'`. (Phase 7's switch, SW1, 2026-11-24) The server's
streams `sms`, each meeting grpc's stream run contract at its content, are registered by the start;
until then it gave the stream server `grpcStreamServerAt` to `ak_served_watch`. -/
theorem ak_served_kv (addr : GoString) (gs q p pa s : Loc) (lis : GoInterface)
    (E : apply.AEnv GF) (ρ : ReqNames) (cid mid n : w64) (il im iu ims is : GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × GoFunc × GoInterface))
    (sms : List (GrpcStreamMethod GF))
    (γa : auth.AuthNames) (hγa : E.authMode = .on γa)
    (hregs : ∀ x ∈ v3rpc.kvRegs q, x ∈ regs) (hregsA : ∀ x ∈ v3rpc.authRegs pa, x ∈ regs)
    (hsms : ∀ m ∈ sms, (m.name, m.handler, m.srv) ∈ sregs) (hsnd : (sms.map (·.name)).Nodup)
    (wpBC : auth.authStore.BcryptCost.spec (GF := GF)) (Hrf : grpcRepliesFit)
    (hnd : ((regs ++ sregs).map Prod.fst).Nodup) (HL : srvLevels (GF := GF)) :
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
        srvInterceptorOk iu (levelTok 0) v3rpc.learnerReqOk ∗
        grpcSrvNew gs [il, im, iu] [ims, is] svcs regs sregs ∗ netListenerAt lis addr ∗ netAddrLeft addr ∗
        srvRevokeBuilt s E ∗ srvRunPool s E ρ.rd ∗
        (□ [∗list] m ∈ sms, grpcStreamRunOk #m.handler m.srv [ims, is] m.Up m.spec ∗
          □ ∀ md γ, m.spec md γ (m.dn md γ)) ⊢
      |={⊤}=> grpcServeTok gs lis addr (grpcStartSvc [il, im, iu] regs etcdTys sms) ∗
        ([∗list] m ∈ sms, isGrpcStreamMd addr m.name m.Up m.spec) ∗
        akKVOn addr s E ρ cid mid ∗ setupAuthServed addr s E ρ ∗
        isGrpcRpc addr authnMethod (client.etcdAuthenticateSpec γa) ∗
        grpcServerAt addr [il, im, iu] regs etcdTys sms := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hlb, #Hat, #HNR, #Hq, #Hpa, #HBF, #Hil, #Him, #Hiu, Hgs,
    Hlis, Hleft, #Hb, #Hrp, #Hsms⟩
  imod (grpc.start' gs lis addr [il, im, iu] [ims, is] svcs regs sregs etcdTys etcdTys_reg sms hsms
      hsnd Hrf hnd) $$ [Hgs Hlis Hleft]
    with ⟨#Hat', #Hss, Htok⟩
  · iframe Hgs Hlis Hleft Hsms
  iunfold srvAuthStoreOn at HBF
  icases HBF with ⟨%stl, %c, #Hfld, #Hc, #Hau⟩
  ihave #Hbc := bcryptCostOk_of_field wpBC stl c $$ Hc
  ihave #Hil' := Hil $$ %v3rpc.learnerReqOk
  ihave #Him' := Him $$ %v3rpc.learnerReqOk
  imod (client.etcd_kv_auth_served_on addr p q pa s E ρ ρ.rd cid mid n il im iu
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty, #stl⟩ regs sms γa hγa
      (by
        intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hregs x h
        · exact hregsA x h) HL) $$ []
    with ⟨#Hput, #Hrange, #Hdel, #Htxn, #Hua, #Hug, #Hra, #Hrg, #Hae, #Hauth⟩
  · iframe; iframe #
  imodintro
  iframe Htok Hss Hauth Hat'
  isplitl []
  · unfold akKVOn
    iframe #
  unfold setupAuthServed
  iframe #


/-- **etcd's server, started for authkv: its watch service** (see the file header): watchkv's
`wk_served_nd`'s watch half, with the members' KV facts from the read view with auth on. (Phase 7's
switch, SW1, 2026-11-24) From the `Watch` stream's registration, which the start makes
(`ak_served_kv`, from `v3rpc.etcd_watch_served_chain`'s run contract): until then from the stream
server `grpcStreamServerAt`, the chain's contracts and the run pools. -/
theorem ak_served_watch [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (Hp : mvcc.api.persistent.law (GF := GF))
    (V : client.WEnv GF) (addr : GoString) (pw s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (hV : V.addr = addr) (hE : V.R.E = E) (hs : V.R.s = s) (hp : V.pfx ≠ []) (hst : kvSame γr.kv V.kv)
    (hlog : γr.kv.log0 = [[], []]) (hrb : receiptBound GF ≤ 2 ^ 62)
    -- (R9, the `lean` merge) the watch contract at the server's model and watch facts
    (hWM : V.WM = v3rpc.etcdModelOfServer V.R.E γr true) (hWL : V.WL = client.srvWL V.W)
    (hH : V.W.histLb = srvApi.histLb γr true V.R.E.γs) (hC : V.W.crevOk = srvApi.crevOk γr) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isServerReadM true s E γr ∗ v3rpc.isWatchServer pw V.R ∗
        v3rpc.srvWOk V.W V.R.wsl v3rpc.wsN ∗
        ([∗list] m ∈ [v3rpc.watchMethod pw V.R V.W], isGrpcStreamMd addr m.name m.Up m.spec) ∗
        client.eofOk ⊢
      |={⊤}=> watchAddrFacts V ∗ auth.modeTag V.R.tag E.authMode := by
  haveI := v3rpc.srvWOk_persistent Hp V.W V.R.wsl v3rpc.wsN
  iintro ⟨#Ppb, #Pv, #Hrd, #Hws, #HW, #Hss, #Heof⟩
  ihave #Htag : auth.modeTag V.R.tag E.authMode $$ []
  · iunfold v3rpc.isWatchServer at Hws
    icases Hws with ⟨-, -, -, -, -, -, -, -, -, #Hok⟩
    iunfold v3rpc.watchSrvOk at Hok
    icases Hok with ⟨-, -, -, #Ht, -⟩
    rw [← hE]; iexact Ht
  ihave #Hst := BigSepL.bigSepL_singleton.1 $$ Hss
  try simp only [v3rpc.watchMethod, v3rpc.pbWatchRequestT, v3rpc.pbWatchResponseT]
  ihave #Hcore := srvKVCoreM_of_readM true s E γr $$ Hrd
  ihave #Hkf := client.srvKVFacts_intro V true γr hst hlog hrb hH hC $$ [Hcore]
  · rw [hE]; iframe #
  ihave #Hwl := client.srvWLaws_of_ok V.W V.R.wsl v3rpc.wsN $$ HW
  ihave #Hlaws := client.watchLaws_srv V true γr hWM hWL hH $$ Hwl
  -- auth on: the cluster never compacts (`srvKVInvsOn`'s mode)
  ihave %Hcm : ⌜γr.kv.cmp = false⌝ $$ []
  · iunfold isServerReadM at Hrd
    icases Hrd with ⟨%v, Hrd⟩
    iunfold srvReadFieldsAtM at Hrd
    icases Hrd with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hkvi, -⟩
    ihave #Hon := srvKVInvsM_true s E γr $$ Hkvi
    iunfold srvKVInvsOn at Hon
    icases Hon with ⟨-, -, -, -, -, -, -, %Hm, -⟩
    ipureintro; exact Hm.1
  ihave #Honce := client.srvOnce_noCmp V.W γr hC Hcm
  imodintro
  iframe Htag
  unfold watchAddrFacts
  rw [hV]
  iframe #
  ipureintro; exact hp

end served

end etcd_auth
end EtcdGrove
end Perennial
