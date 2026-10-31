/-
**etcd's server serves `Authenticate` with auth on** (the auth plan's C1, layer 4, 2026-10-28;
`notes/c1-plan.md`): the spec it registers for `Auth.Authenticate` (`etcdAuthenticateSpec`: a
reply's token is issued to the user named, `auth.tokIssued`), and what a client's `New` takes of it
(`authTokReg_of`: `clientAuthPre`'s registration at the tokens issued to the user). Lean-first (no
Rocq counterpart).

`etcd_kv_auth_served_on`: the KV methods with auth on, the Auth service's admin methods and
`Authenticate` served by one gRPC server (C1's A5, 2026-10-31; it replaced the stub
`etcd_kv_auth_served_onA` and the earlier `etcd_kv_auth_served_on` without `Authenticate`): the handler (`etcd_authenticateHandlerOk`) is `AuthServer.Authenticate` over the
server's `Authenticate` with auth on (`server_authenticate_on`), at its run slot `authnSlot` (the
four readers `EtcdServer.Authenticate` takes, a part of the KV's `etcdGrpcSlot`:
`etcdGrpcSlot_authn`); its auth store's `Authenticate` side (`authnStoreOk`) is the one premise it
adds.

**The replies' size** (2026-10-31, `notes/reply-size.md`): these results take a server token
(`grpcServerAt`), made only by `grpc.start`, which takes the workload premise `grpcRepliesFit`;
they are conditional on it through the token, which their statements do not show.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ServedOn
public import Proof.go_etcd_io.etcd.client.v3.ClientUser
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Results

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

/-- **`Authenticate`'s run slot** (`EtcdServer.Authenticate`'s readers: of `s.leadTimeMu`, `s.lgMu`,
the read loop's lock, and the server's reader resource), given back. -/
def authnSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ srvLgReader s ∗ srvReadReader s γr ∗ E.RD)

/-- **What the server's `Authenticate` answers `AuthServer.Authenticate`** (before `togRPCError`):
the run's slot, the request's password field, and on `nil` a response whose token was issued to
`name`. -/
def authnAns (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γa : auth.AuthNames) (r : Loc)
    (name : GoString) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(authnSlot s E γr ∗
    (∃ pw' : GoString, structFieldRef etcdserverpb.AuthenticateRequest go!"Password" r ↦ pw') ∗
    (⌜err = GoInterface.nil⌝ -∗ ∃ v : etcdserverpb.AuthenticateResponse,
      resp ↦ v ∗ auth.tokIssued γa v.Token' name))

/-- **etcd's `Authenticate`, as the service runs it, with auth on at `γa`** (`grpcHandlerOwnOk`; C1's
A5): the `*AuthServer` `p` of the server `s` in the mode `on` (`isServerReqM true`,
`isServerReadM true`, the id budget), whose auth store `ast` meets `authnStoreOk`: given the run's
slot (`authnSlot`), the decoded request (its `Password` the run's own) and `etcdAuthenticateSpec`,
its slot back and on success a reply whose token was issued to the user named. -/
theorem etcd_authenticateHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γa : auth.AuthNames) (hγa : E.authMode = .on γa) (ast : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗
        □ (|==> idCred ρ.ids 1) ∗
        structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗
        authnStoreOk (GoInterface.ok ast) E.RD ⊢
      grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"Authenticate")
        (authnSlot s E γr) (GrpcSpec.md (etcdAuthenticateSpec γa)) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #Hrdv, #HNR, #Hast, #Hauthn⟩
  unfold grpcHandlerOwnOkMd
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hpw, Hspec⟩ HΨ
  simp only [pbAuthenticateRequest]
  icases Hr with ⟨%Hrn, #HN⟩
  iunfold authnSlot at Hslot
  icases Hslot with ⟨Hlt, Hlg, Hrr, Hrd⟩
  imod (mvcc.idxCert_nil (GF := GF) E.γ.idx) with #HF
  ihave #Hin : v3rpc.authInnerOk s go!"Authenticate" (GoInterface.ok ci) r
      iprop(structFieldRef etcdserverpb.AuthenticateRequest go!"Password" r ↦ m.2 ∗
        srvLeadTimeReader s ∗ srvLgReader s ∗ srvReadReader s γr ∗ E.RD)
      (authnAns s E γr γa r m.1) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ' ⟨Hpw', Hlt', Hlg', Hrr', Hrd'⟩ HΨ'
    iapply (server_authenticate_on s E ρ γr γa ci cd ast r m.1 m.2 [] hγa)
      $$ [Hpw' Hlt' Hlg' Hrr' Hrd']
    · iframe Hpw' Hlt' Hlg' Hrr' Hrd'; iframe #
      ipureintro; exact Hrn
    inext
    iintro %resp %err ⟨Hlt', Hlg', Hrr', Hrd', ⟨%pw', Hpw', -⟩, #HaE, Hout⟩
    iapply HΨ'
    iframe HaE
    iunfold authEntryOut
    icases Hout with (⟨%He, %v, Hv, #Ht⟩ | %Hre)
    · subst He
      ileft
      isplitr
      · ipureintro; rfl
      iunfold authnAns
      iunfold authnSlot
      iframe Hlt' Hlg' Hrr' Hrd'
      isplitl [Hpw']
      · iexists pw'; iexact Hpw'
      iintro -
      iexists v
      iframe Hv Ht
    · obtain ⟨rfl, Hne⟩ := Hre
      iright
      isplitr
      · ipureintro; exact ⟨rfl, Hne⟩
      iunfold authnAns
      iunfold authnSlot
      iframe Hlt' Hlg' Hrr' Hrd'
      isplitl [Hpw']
      · iexists pw'; iexact Hpw'
      iintro %He
      exact absurd He Hne
  iapply (v3rpc.AuthServer.wp_Authenticate p s ci r
      iprop(structFieldRef etcdserverpb.AuthenticateRequest go!"Password" r ↦ m.2 ∗
        srvLeadTimeReader s ∗ srvLgReader s ∗ srvReadReader s γr ∗ E.RD)
      (authnAns s E γr γa r m.1)) $$ [Hpw Hlt Hlg Hrr Hrd]
  · iframe #; iframe Hpw Hlt Hlg Hrr Hrd
  inext
  iintro %resp %err Hout
  iapply HΨ
  iunfold v3rpc.authWrapOut at Hout
  icases Hout with (⟨%He, Ha⟩ | ⟨%Hre, %e0, %He0, Ha⟩)
  · iunfold authnAns at Ha
    icases Ha with ⟨Hs, -, Hok⟩
    iframe Hs
    iintro -
    ihave ⟨%v, Hv, #Ht⟩ := Hok $$ %rfl
    iexists v.Token'
    simp only [pbAuthenticateResponse]
    isplitl [Hv]
    · iexists v; iframe Hv; ipureintro; rfl
    iunfold etcdAuthenticateSpec at Hspec
    iapply Hspec
    iexact Ht
  · iunfold authnAns at Ha
    icases Ha with ⟨Hs, -, -⟩
    iframe Hs
    iintro %He
    exact absurd He Hre.2

/-- **etcd's `Authenticate`, as grpc runs it** (`grpcMethodOk`; as `etcd_userAddMethodOk`): the
generated `_Auth_Authenticate_Handler` on the `*AuthServer` `p` whose `Authenticate` meets etcd's
spec, under a chain of transparent interceptors. -/
theorem etcd_authenticateMethodOk (p : Loc)
    (Spec : GrpcSpecMd (GF := GF) pbAuthenticateRequest pbAuthenticateResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"Authenticate") S Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._Auth_Authenticate_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthenticateRequest) -∗
      (pbAuthenticateRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthenticateRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbAuthenticateRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthenticateRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthenticateRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_Authenticate_Handler pbAuthenticateRequest pbAuthenticateResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.authServer_isAuthServer)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- The KV methods' run slot is `Authenticate`'s (`authnSlot` and the interceptors'), with the rest
of the KV handlers' slot and the quota check's. -/
theorem etcdGrpcSlot_authn (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    etcdGrpcSlot (GF := GF) s E γr ⊣⊢
      iprop((authnSlot s E γr ∗ [∗list] R ∈ etcdIcRs s, R) ∗
        (mvcc.storeReader E.s E.γ ∗ v3rpc.quotaRd s)) := by
  unfold etcdGrpcSlot etcdRunSlot authnSlot
  constructor
  · iintro ⟨⟨⟨Hlt, Hsr, Hlg, Hrd, Hard⟩, Hq⟩, Hics⟩
    iframe
  · iintro ⟨⟨⟨Hlt, Hlg, Hrd, Hard⟩, Hics⟩, Hsr, Hq⟩
    iframe

/-- **`Authenticate`'s method as registered**, with etcd's spec at `γa`. -/
def etcdAuthnMethod (pa : Loc) (γa : auth.AuthNames) : GrpcMethod GF :=
  ⟨authnMethod, pbAuthenticateRequest, pbAuthenticateResponse, GrpcSpec.md (etcdAuthenticateSpec γa),
    (@! etcdserverpb._Auth_Authenticate_Handler),
    interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #pa⟩

/-- **etcd's server serves its KV methods with auth on, its Auth methods and `Authenticate`** (see
the file header; one gRPC server, as `grpc.serve` takes every served method at once): the gRPC
server at `addr` serves the KV methods with auth on, the Auth service's admin methods, and
`Authenticate` with etcd's spec at the member's names `γa` (`etcdAuthenticateSpec`), its
registration in `v3rpc.authRegs`. Premises: the server's with auth on, the `*AuthServer` over it,
its auth store's bcrypt cost (`bcryptCostOk`) and `Authenticate` side (`authnStoreOk`, at the server's reader resource). -/
theorem etcd_kv_auth_served_on (addr : GoString) (p q pa s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64) (il im iu : GoFunc)
    (ast : GoInterfaceOk) (regs : List (GoString × val × GoInterface)) (N : Nat)
    (γa : auth.AuthNames) (hγa : E.authMode = .on γa)
    (hregs : ∀ x ∈ etcdKVRegs (GF := GF) q ++ v3rpc.authRegs pa, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        v3rpc.authServerIs pa s ∗
        structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗ bcryptCostOk ast ∗
        authnStoreOk (GoInterface.ok ast) E.RD ∗
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
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hlb, #Hat, #HNR, #Hq, #Has, #Hast, #Hcost, #Hauthn, #Hil, #Him,
    #Hiu, Hl, Hslots⟩
  ihave #Hp := etcd_putHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Hr := etcd_rangeHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Hd := etcd_deleteHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Ht := etcd_txnHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Hqt := v3rpc.quotaKV_txnHandlerOkMd_of v3rpc.quotaKVServer.wp_Txn (etcdTxnSpecOn s E ρ γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hqp := v3rpc.quotaKV_putHandlerOkMd_of v3rpc.quotaKVServer.wp_Put (etcdPutSpecOn s E ρ cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hr' := grpcHandlerOkMd_frame _ _ (v3rpc.quotaRd s) (etcdRangeSpecOn s E γr cid mid) $$ Hr
  ihave #Hd' := grpcHandlerOkMd_frame _ _ (v3rpc.quotaRd s) (etcdDeleteSpecOn s E ρ cid mid) $$ Hd
  ihave #Hqr := v3rpc.quotaKV_promotedHandlerOkMd (etcdRangeSpecOn s E γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ v3rpc.quotaRd s) go!"Range" inferInstance $$ [Hq Hr']
  · iframe #
  ihave #Hqd := v3rpc.quotaKV_promotedHandlerOkMd (etcdDeleteSpecOn s E ρ cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ v3rpc.quotaRd s) go!"DeleteRange" inferInstance $$ [Hq Hd']
  · iframe #
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmp := etcd_putMethodOn q _ _ _ (etcdPutSpecOn s E ρ cid mid) $$ [Hqp Ppb Hics]
  · iframe #
  ihave #Hmr := etcd_rangeMethodOn q _ _ _ (etcdRangeSpecOn s E γr cid mid) $$ [Hqr Ppb Hics]
  · iframe #
  ihave #Hmd := etcd_deleteMethodOn q _ _ _ (etcdDeleteSpecOn s E ρ cid mid) $$ [Hqd Ppb Hics]
  · iframe #
  ihave #Hmt := etcd_txnMethodOn q _ _ _ (etcdTxnSpecOn s E ρ γr cid mid) $$ [Hqt Ppb Hics]
  · iframe #
  -- the Auth methods, at their slot (`authSlot` and the interceptors'), then at the KV's
  ihave #Hu := v3rpc.etcd_userAddHandlerOk pa s E ρ ast $$ []
  · iframe #
  ihave #Hg := v3rpc.etcd_userGrantRoleHandlerOk pa s E ρ $$ []
  · iframe #
  ihave #Hra := v3rpc.etcd_roleAddHandlerOk pa s E ρ $$ []
  · iframe #
  ihave #Hrp := v3rpc.etcd_roleGrantPermissionHandlerOk pa s E ρ $$ []
  · iframe #
  ihave #He := v3rpc.etcd_authEnableHandlerOk pa s E ρ $$ []
  · iframe #
  ihave #Hn := etcd_authenticateHandlerOk pa s E ρ γr γa hγa ast $$ []
  · iframe #
  ihave #Hmu := v3rpc.etcd_userAddMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$ [Hu Ppb Hics]
  · iframe #
  ihave #Hmg := v3rpc.etcd_userGrantRoleMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$ [Hg Ppb Hics]
  · iframe #
  ihave #Hmra := v3rpc.etcd_roleAddMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$ [Hra Ppb Hics]
  · iframe #
  ihave #Hmrp := v3rpc.etcd_roleGrantPermissionMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$
    [Hrp Ppb Hics]
  · iframe #
  ihave #Hme := v3rpc.etcd_authEnableMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$ [He Ppb Hics]
  · iframe #
  ihave #Hmn := etcd_authenticateMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$ [Hn Ppb Hics]
  · iframe #
  have hs1 := (etcdGrpcSlot_auth (GF := GF) s E γr).1
  have hs2 := (etcdGrpcSlot_auth (GF := GF) s E γr).2
  ihave #Hmu' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hs1 hs2 $$ Hmu
  ihave #Hmg' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hs1 hs2 $$ Hmg
  ihave #Hmra' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hs1 hs2 $$ Hmra
  ihave #Hmrp' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hs1 hs2 $$ Hmrp
  ihave #Hme' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hs1 hs2 $$ Hme
  have hn1 := (etcdGrpcSlot_authn (GF := GF) s E γr).1
  have hn2 := (etcdGrpcSlot_authn (GF := GF) s E γr).2
  ihave #Hmn' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hn1 hn2 $$ Hmn
  imod (grpc_serve_rpcs addr [il, im, iu] regs (etcdKVMethodsOn q s E ρ γr cid mid ++
      v3rpc.etcdAuthMethods pa s E ρ ++ [etcdAuthnMethod pa γa])
    (etcdGrpcSlot s E γr) N
    (by simp only [etcdKVMethodsOn, v3rpc.etcdAuthMethods, etcdAuthnMethod, authnMethod, List.map,
          List.cons_append, List.nil_append]
        decide)
    (by
      intro x hx
      apply hregs
      simp only [etcdKVMethodsOn, v3rpc.etcdAuthMethods, etcdAuthnMethod, List.cons_append,
        List.nil_append, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [etcdKVRegs, v3rpc.authRegs, authnMethod]))
    $$ [Hl Hslots] with Hrpcs
  · iframe
    imodintro
    simp only [etcdKVMethodsOn, v3rpc.etcdAuthMethods, etcdAuthnMethod, List.cons_append,
      List.nil_append]
    unfold etcdGrpcSlot
    iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  simp only [etcdKVMethodsOn, v3rpc.etcdAuthMethods, etcdAuthnMethod, List.cons_append,
    List.nil_append]
  icases Hrpcs with ⟨#H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9, #H10, -⟩
  imodintro
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9
  iapply (isGrpcRpc_md _ _ _).2
  iexact H10

end proofs

end client
end EtcdGrove
end Perennial
