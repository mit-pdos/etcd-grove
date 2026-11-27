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

`etcd_lease_auth_served_on` (auth-lease S3c, 2026-11-15): the Lease service's `LeaseGrant` and
`LeaseRevoke` with auth on, in the revocable lease mode, at etcd's metadata specs
(`etcdLeaseGrantSpecOn`, `etcdLeaseRevokeSpecOn`, `LeaseGrantServed.lean`), from the same server
token, so that a caller serves them beside the KV and Auth methods.

**The replies' size** (2026-10-31, `notes/reply-size.md`): these results take a server token
(`grpcServerAt`), made only by the single-process start (`grpc.start'`), which takes the workload premise `grpcRepliesFit`;
they are conditional on it through the token, which their statements do not show.
-/
module

public import Proof.context.ReqKeys
public import Proof.go_etcd_io.etcd.client.v3.ClientUser
public import Proof.go_etcd_io.etcd.client.v3.LeaseGrantServed
public import Proof.go_etcd_io.etcd.client.v3.AuthnSpec
public import Proof.go_etcd_io.etcd.client.v3.ServeLaws
public import Proof.go_etcd_io.etcd.client.v3.GrpcTys

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
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

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
    unfold etcdAuthenticateSpec etcdAuthenticateSpecW
    iintro %t #Ht !>
    iexact Ht

theorem authTokReg_of_law_holds : authTokReg_of.law (GF := GF) (hG := hG) :=
  authTokReg_of

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
      resp ↦ v ∗ ⌜v.unknownFields' = slice.nil⌝ ∗ auth.tokIssued γa v.Token' name))

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
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hpw, Hspec⟩ HΨ
  ihave ⟨Hspec, #HΨe⟩ := grpcSpecAt_md_elim _ _ _ _ _ $$ Hspec
  simp only [pbAuthenticateRequest]
  icases Hr with ⟨%Hrn, #HN⟩
  iunfold authnSlot at Hslot
  icases Hslot with ⟨Hlt, Hlg, Hrr, Hrd⟩
  imod (v3rpc.kvLogLb_nil (GF := GF) E.γs) with #HF
  ihave #Hspan := spanCtxOk_of_runCtx ci $$ Hrc
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc
  ihave #Hst := startTimeOk_of_grpcRunCtx ci $$ Hrc
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
    icases Hout with (⟨%He, %v, Hv, %Hvu, #Ht⟩ | %Hre)
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
      ipureintro; exact Hvu
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
  ihave ⟨#HSe, Hout⟩ := v3rpc.authWrapOut_srvErrOk _ resp err $$ Hout
  ihave Hed := handlerErrOut_allSrv (GF := GF) Ψe err $$ HΨe HSe
  iapply HΨ
  iframe Hed HSe
  iunfold v3rpc.authWrapOut at Hout
  icases Hout with (⟨%He, Ha⟩ | ⟨%Hre, -, %e0, %He0, Ha⟩)
  · iunfold authnAns at Ha
    icases Ha with ⟨Hs, -, Hok⟩
    iframe Hs
    iintro -
    ihave ⟨%v, Hv, %Hvu, #Ht⟩ := Hok $$ %rfl
    iexists v.Token'
    simp only [pbAuthenticateResponse]
    isplitl [Hv]
    · iexists v; iframe Hv; ipureintro; exact ⟨rfl, Hvu⟩
    iunfold etcdAuthenticateSpec, etcdAuthenticateSpecW at Hspec
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
    grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"Authenticate")
        iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._Auth_Authenticate_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthenticateRequest) -∗
      (pbAuthenticateRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthenticateRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbAuthenticateRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthenticateRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthenticateRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_Authenticate_Handler pbAuthenticateRequest pbAuthenticateResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk m Φ Ψe ci cd dec ui rfl rfl v3rpc.authServer_isAuthServer)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres, Hed⟩
  iapply HΨ
  iframe

/-- The KV methods' run slot is the Auth methods' (`authSlot` and the interceptors'), with the rest
of the KV handlers' slot and the quota check's `bemu` reader (per-type stage B3: the `lgMu` reader is
the interceptors'). -/
theorem etcdGrpcSlot_auth (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    etcdGrpcSlot (GF := GF) s E γr ⊣⊢
      iprop((v3rpc.authSlot s E ∗ [∗list] R ∈ etcdIcRs s, R) ∗
        (mvcc.api.mvccReaders E.γ 1 ∗ srvReadReader s γr ∗ srvBemuReader s)) := by
  unfold etcdGrpcSlot etcdKVSlot v3rpc.authSlot
  constructor
  · iintro ⟨⟨⟨Hlt, Hsr, Hrd, Hard⟩, Hb⟩, Hics⟩
    iframe
  · iintro ⟨⟨⟨Hlt, Hard⟩, Hics⟩, Hsr, Hrd, Hb⟩
    iframe

/-- The KV methods' run slot is `Authenticate`'s handler's (`authnSlot` without the `lgMu` reader,
which the interceptors lend, and the interceptors'), with the rest of the KV handlers' slot and the
quota check's `bemu` reader. -/
theorem etcdGrpcSlot_authn (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    etcdGrpcSlot (GF := GF) s E γr ⊣⊢
      iprop((iprop(srvLeadTimeReader s ∗ srvReadReader s γr ∗ E.RD) ∗ [∗list] R ∈ etcdIcRs s, R) ∗
        (mvcc.api.mvccReaders E.γ 1 ∗ srvBemuReader s)) := by
  unfold etcdGrpcSlot etcdKVSlot
  constructor
  · iintro ⟨⟨⟨Hlt, Hsr, Hrd, Hard⟩, Hb⟩, Hics⟩
    iframe
  · iintro ⟨⟨⟨Hlt, Hrd, Hard⟩, Hics⟩, Hsr, Hb⟩
    iframe

/-- `grpcHandlerOwnOk_slot`'s, for an owning metadata-indexed service method. -/
theorem grpcHandlerOwnOkMd_slot {Req Rep : ProtoMsg GF} (h : val) (S S' F : IProp GF)
    (Spec : GrpcSpecMd Req Rep) (h1 : S' ⊢ S ∗ F) (h2 : S ∗ F ⊢ S') :
    grpcHandlerOwnOkMd h S Spec ⊢ grpcHandlerOwnOkMd h S' Spec := by
  iintro #Hh
  unfold grpcHandlerOwnOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨HS', #Hctx, #Hrc, #Hr, Hown, HSpec⟩ HΨ
  ihave ⟨HS, HF⟩ := h1 $$ HS'
  iapply Hh $$ %m %Φ %Ψe %ci %cd %r [HS Hown HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe Hres
  iapply h2
  iframe

/-- `Authenticate`'s slot is its handler's part of the run's slot with the interceptors' lent
resources (`etcdIcRs`, whose `lgMu` reader is `authnSlot`'s), and the lent level-0 token. -/
theorem authnSlot_lent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    iprop(iprop(srvLeadTimeReader s ∗ srvReadReader s γr ∗ E.RD) ∗ [∗list] R ∈ etcdIcRs (GF := GF) s, R) ⊣⊢
      iprop(authnSlot s E γr ∗ levelTok 0) := by
  unfold authnSlot
  constructor
  · iintro ⟨⟨Hlt, Hrr, Hrd⟩, Hl⟩
    icases (etcdIcRs_eq s).1 $$ Hl with ⟨Hlg, H0⟩
    iframe
  · iintro ⟨⟨Hlt, Hlg, Hrr, Hrd⟩, H0⟩
    iframe
    iapply (etcdIcRs_eq s).2
    iframe

/-- **`Authenticate`'s method as registered**, with etcd's spec at `γa`. -/
def etcdAuthnMethod (pa : Loc) (γa : auth.AuthNames) : GrpcMethod GF :=
  ⟨authnMethod, pbAuthenticateRequestT, pbAuthenticateResponseT, GrpcSpec.md (etcdAuthenticateSpec γa),
    (functions etcdserverpb._Auth_Authenticate_Handler []),
    interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #pa,
    pbAuthenticateRequestT_reg, pbAuthenticateResponseT_reg⟩

/-- **etcd's server serves its KV methods with auth on, its Auth methods and `Authenticate`** (see
the file header; one gRPC server, as `grpc.serve` takes every served method at once): the gRPC
server at `addr` serves the KV methods with auth on, the Auth service's admin methods, and
`Authenticate` with etcd's spec at the member's names `γa` (`etcdAuthenticateSpec`), its
registration in `v3rpc.authRegs` (per-type stage B3: the server at `addr` with the streams `sms`, each run on a fork of grpc's
borrowing from the server's built pools and run pool, `srvRevokeBuilt`, `srvRunPool`, with the
levels `srvLevels`). Premises: the server's with auth on, the `*AuthServer` over it,
its auth store's bcrypt cost (`bcryptCostOk`) and `Authenticate` side (`authnStoreOk`, at the server's reader resource). -/
theorem etcd_kv_auth_served_on (addr : GoString) (p q pa s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64) (il im iu : GoFunc)
    (ast : GoInterfaceOk) (regs : List (GoString × GoFunc × GoInterface)) (sms : List (GrpcStreamMethod GF))
    (γa : auth.AuthNames) (hγa : E.authMode = .on γa)
    (hregs : ∀ x ∈ etcdKVRegs (GF := GF) q ++ v3rpc.authRegs pa, x ∈ regs)
    (HL : srvLevels (GF := GF)) :
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
        srvInterceptorOk iu (levelTok 0) v3rpc.learnerReqOk ∗
        grpcServerAt addr [il, im, iu] regs etcdTys sms ∗ srvRevokeBuilt s E ∗ srvRunPool s E γr ⊢
      |={⊤}=> isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn (srvTLSId s) E ρ cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn (srvTLSId s) E γr cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpecOn (srvTLSId s) E ρ cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpecOn (srvTLSId s) E ρ γr cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/UserAdd" (v3rpc.etcdUserAddSpec (srvTLSId s) E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/UserGrantRole" (v3rpc.etcdUserGrantRoleSpec (srvTLSId s) E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/RoleAdd" (v3rpc.etcdRoleAddSpec (srvTLSId s) E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/RoleGrantPermission"
          (v3rpc.etcdRoleGrantPermissionSpec (srvTLSId s) E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/AuthEnable" (v3rpc.etcdAuthEnableSpec (srvTLSId s) E ρ) ∗
        isGrpcRpc addr authnMethod (etcdAuthenticateSpec γa) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hlb, #Hat, #HNR, #Hq, #Has, #Hast, #Hcost, #Hauthn, #Hil, #Him,
    #Hiu, #Hl, #Hb, #Hrpl⟩
  have hon : E.authOn = true := by unfold apply.AEnv.authOn; rw [hγa]; rfl
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
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
  ihave #Hu := v3rpc.grpcHandlerOwnOkMd_frame _ _ iprop([∗list] R ∈ etcdIcRs s, R) _ $$ Hu
  ihave #Hg := v3rpc.grpcHandlerOwnOkMd_frame _ _ iprop([∗list] R ∈ etcdIcRs s, R) _ $$ Hg
  ihave #Hra := v3rpc.grpcHandlerOwnOkMd_frame _ _ iprop([∗list] R ∈ etcdIcRs s, R) _ $$ Hra
  ihave #Hrp := v3rpc.grpcHandlerOwnOkMd_frame _ _ iprop([∗list] R ∈ etcdIcRs s, R) _ $$ Hrp
  ihave #He := v3rpc.grpcHandlerOwnOkMd_frame _ _ iprop([∗list] R ∈ etcdIcRs s, R) _ $$ He
  ihave #Hn := grpcHandlerOwnOkMd_slot _ (authnSlot s E γr)
    iprop(iprop(srvLeadTimeReader s ∗ srvReadReader s γr ∗ E.RD) ∗ [∗list] R ∈ etcdIcRs s, R)
    (levelTok 0) _ (authnSlot_lent s E γr).1 (authnSlot_lent s E γr).2 $$ Hn
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
  ihave #Hmn := etcd_authenticateMethodOk pa _
    iprop(srvLeadTimeReader s ∗ srvReadReader s γr ∗ E.RD) [il, im, iu] (etcdIcRs s)
    $$ [Hn Ppb Hics]
  · iframe #
  have hs1 := (etcdGrpcSlot_auth (GF := GF) s E γr).1
  have hs2 := (etcdGrpcSlot_auth (GF := GF) s E γr).2
  ihave #Hmu' := grpcMethodOkMd_slot _ _ _ _ (etcdGrpcSlot s E γr) _ _ hs1 hs2 $$ Hmu
  ihave #Hmg' := grpcMethodOkMd_slot _ _ _ _ (etcdGrpcSlot s E γr) _ _ hs1 hs2 $$ Hmg
  ihave #Hmra' := grpcMethodOkMd_slot _ _ _ _ (etcdGrpcSlot s E γr) _ _ hs1 hs2 $$ Hmra
  ihave #Hmrp' := grpcMethodOkMd_slot _ _ _ _ (etcdGrpcSlot s E γr) _ _ hs1 hs2 $$ Hmrp
  ihave #Hme' := grpcMethodOkMd_slot _ _ _ _ (etcdGrpcSlot s E γr) _ _ hs1 hs2 $$ Hme
  have hn1 := (etcdGrpcSlot_authn (GF := GF) s E γr).1
  have hn2 := (etcdGrpcSlot_authn (GF := GF) s E γr).2
  ihave #Hmn' := grpcMethodOkMd_slot _ _ _ _ (etcdGrpcSlot s E γr) _ _ hn1 hn2 $$ Hmn
  -- the Auth methods and `Authenticate` at the KV's slot, then as grpc runs them (the run pools)
  ihave #Hms : iprop(□ [∗list] m ∈ v3rpc.etcdAuthMethods pa s E ρ ++ [etcdAuthnMethod pa γa],
      grpcMethodOkMd #m.handler m.srv [il, im, iu] (etcdGrpcSlot s E γr) m.spec) $$ []
  · iintro !>
    unfold v3rpc.etcdAuthMethods etcdAuthnMethod
    simp only [List.cons_append, List.nil_append]
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbAuthUserAddRequest)
        (Rep := pbAuthUserAddResponse) (@! etcdserverpb._Auth_UserAdd_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #pa)
        [il, im, iu] (etcdGrpcSlot s E γr) (v3rpc.etcdUserAddSpec (srvTLSId s) E ρ))
      iexact Hmu'
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbAuthUserGrantRoleRequest)
        (Rep := pbAuthUserGrantRoleResponse) (@! etcdserverpb._Auth_UserGrantRole_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #pa)
        [il, im, iu] (etcdGrpcSlot s E γr) (v3rpc.etcdUserGrantRoleSpec (srvTLSId s) E ρ))
      iexact Hmg'
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbAuthRoleAddRequest)
        (Rep := pbAuthRoleAddResponse) (@! etcdserverpb._Auth_RoleAdd_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #pa)
        [il, im, iu] (etcdGrpcSlot s E γr) (v3rpc.etcdRoleAddSpec (srvTLSId s) E ρ))
      iexact Hmra'
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbAuthRoleGrantPermissionRequest)
        (Rep := pbAuthRoleGrantPermissionResponse) (@! etcdserverpb._Auth_RoleGrantPermission_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #pa)
        [il, im, iu] (etcdGrpcSlot s E γr) (v3rpc.etcdRoleGrantPermissionSpec (srvTLSId s) E ρ))
      iexact Hmrp'
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbAuthEnableRequest)
        (Rep := pbAuthEnableResponse) (@! etcdserverpb._Auth_AuthEnable_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #pa)
        [il, im, iu] (etcdGrpcSlot s E γr) (v3rpc.etcdAuthEnableSpec (srvTLSId s) E ρ))
      iexact Hme'
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbAuthenticateRequest)
        (Rep := pbAuthenticateResponse) (@! etcdserverpb._Auth_Authenticate_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #pa)
        [il, im, iu] (etcdGrpcSlot s E γr) (GrpcSpec.md (etcdAuthenticateSpec γa)))
      iexact Hmn'
    iapply BigSepL.bigSepL_nil.2
    itrivial
  ihave #Hks := etcd_runOks_of_slot [il, im, iu] s E γr HL
    (v3rpc.etcdAuthMethods pa s E ρ ++ [etcdAuthnMethod pa γa]) $$ [Hms]
  · iframe #
  -- the KV methods in the server's mode (`etcd_kv_servedM_with`), at auth on
  rw [v3rpc.kvServerAt_revR p s (v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none)
    (v3rpc.srvKVAnsM E.authOn s E ρ γr (W64 0) [] .none 0 none) cid mid n rfl]
  imod (etcd_kv_servedM_with addr p q s E ρ γr cid mid n il im iu regs sms
    (v3rpc.etcdAuthMethods pa s E ρ ++ [etcdAuthnMethod pa γa])
    (fun x hx => hregs x (List.mem_append_left _ hx))
    (by
      intro m hm
      apply hregs
      simp only [v3rpc.etcdAuthMethods, etcdAuthnMethod, List.cons_append, List.nil_append,
        List.mem_cons, List.mem_nil_iff, _root_.or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v3rpc.authRegs, authnMethod])
    (by
      intro m hm
      simp only [v3rpc.etcdAuthMethods, etcdAuthnMethod, List.cons_append, List.nil_append,
        List.mem_cons, List.mem_nil_iff, _root_.or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [authnMethod])
    (fun h => by rw [hon] at h; cases h) HL) $$ [] with ⟨#H1, #H2, #H3, #H4, -, Hms⟩
  · rw [hon]
    iframe #
    ipureintro; rw [hγa]; simp
  rw [hon]
  ihave #H1' := isGrpcRpcMd_mono _ _ _ _ (etcdPutSpecM_true (srvTLSId s) E ρ cid mid) $$ H1
  ihave #H2' := isGrpcRpcMd_mono _ _ _ _ (etcdRangeSpecM_true (srvTLSId s) E γr cid mid) $$ H2
  ihave #H3' := isGrpcRpcMd_mono _ _ _ _ (etcdDeleteSpecM_true (srvTLSId s) E ρ cid mid) $$ H3
  ihave #H4' := isGrpcRpcMd_mono _ _ _ _ (etcdTxnSpecM_true (srvTLSId s) E ρ γr cid mid) $$ H4
  simp only [v3rpc.etcdAuthMethods, etcdAuthnMethod, List.cons_append, List.nil_append, pbAuthUserAddRequestT, pbAuthUserAddResponseT, pbAuthUserGrantRoleRequestT, pbAuthUserGrantRoleResponseT, pbAuthRoleAddRequestT, pbAuthRoleAddResponseT, pbAuthRoleGrantPermissionRequestT, pbAuthRoleGrantPermissionResponseT, pbAuthEnableRequestT, pbAuthEnableResponseT, pbAuthenticateRequestT, pbAuthenticateResponseT]
  icases Hms with ⟨#H5, #H6, #H7, #H8, #H9, #H10, -⟩
  imodintro
  iframe H1' H2' H3' H4' H5 H6 H7 H8 H9
  iapply (isGrpcRpc_md _ _ _).2
  iexact H10

/-- **etcd's Lease methods with auth on** as registered (auth-lease S3c, Draft §7.3): `LeaseGrant`
and `LeaseRevoke`, the generated handlers of `Lease_ServiceDesc` on the `*quotaLeaseServer` `q`, at
etcd's metadata specs with auth on (`etcdLeaseGrantSpecOn` at the lessor `mvccLeases E.γ`,
`etcdLeaseRevokeSpecOn`). -/
def etcdLeaseMethodsOn (q s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.Lease/LeaseGrant", pbLeaseGrantRequestT, pbLeaseGrantResponseT,
     etcdLeaseGrantSpecOn (srvTLSId s) E ρ (mvcc.api.mvccLeases E.γ),
     (functions etcdserverpb._Lease_LeaseGrant_Handler []),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseGrantRequestT_reg, pbLeaseGrantResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Lease/LeaseRevoke", pbLeaseRevokeRequestT, pbLeaseRevokeResponseT,
     etcdLeaseRevokeSpecOn (srvTLSId s) E ρ,
     (functions etcdserverpb._Lease_LeaseRevoke_Handler []),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseRevokeRequestT_reg, pbLeaseRevokeResponseT_reg⟩]

/-- **etcd's server serves `LeaseGrant` and `LeaseRevoke` with auth on** (auth-lease S3c, Draft §7.3,
decision C8; as `etcd_kv_auth_served_on`, from the persistent server token `grpcServerAt`, so that the
caller registers the KV and Auth methods too): in the revocable lease mode, the gRPC server at `addr`
serves the Lease service's grant and revocation (registered on the `*quotaLeaseServer` `ql` over the
`*LeaseServer` `pl`, `v3rpc.leaseRegs ql` among the registrations) at etcd's metadata specs with auth
on (`etcdLeaseGrantSpecOn`, `etcdLeaseRevokeSpecOn`), each run on a fork of grpc's borrowing the KV's
run slot from the server's built pools and run pool. The lessor contracts with auth on come from the
server's views with auth on (`v3rpc.lessorGrantOkLiveM_server`, `v3rpc.lessorRevokeOkM_server`; the
auth guard from the views, `srvAuthAt_of_viewsM`). -/
theorem etcd_lease_auth_served_on (addr : GoString) (ql pl s : Loc) (A : v3rpc.KVAns GF)
    (lcid lmid : w64) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (il im iu : GoFunc)
    (regs : List (GoString × GoFunc × GoInterface)) (sms : List (GrpcStreamMethod GF)) (γa : auth.AuthNames)
    (hγa : E.authMode = .on γa) (hlm : ρ.rd.kv.lm = .revocable) (hρ : ρ.rd = γr)
    (hregs : ∀ x ∈ v3rpc.leaseRegs ql, x ∈ regs) (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ □ (|==> idCred ρ.ids 1) ∗
      v3rpc.quotaLeaseServerAt ql
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #pl⟩ s ∗
      v3rpc.leaseServerAt pl s A lcid lmid ∗
      srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗ srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
      srvInterceptorOk iu (levelTok 0) v3rpc.learnerReqOk ∗
      grpcServerAt addr [il, im, iu] regs etcdTys sms ∗ srvRevokeBuilt s E ∗ srvRunPool s E γr ⊢
    |={⊤}=> isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseGrant" (etcdLeaseGrantSpecOn (srvTLSId s) E ρ (mvcc.api.mvccLeases E.γ)) ∗
      isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseRevoke" (etcdLeaseRevokeSpecOn (srvTLSId s) E ρ) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #HNR, #Hq, #Hat, #Hil, #Him, #Hiu, #Hl, #Hb, #Hrpl⟩
  have hon : E.authOn = true := by unfold apply.AEnv.authOn; rw [hγa]; rfl
  have hlg : srvGrantsLeases E ρ := by
    unfold srvGrantsLeases; rw [KVNames.lg_eq, hlm]; decide
  ihave #Hcore := srvKVCoreM_of_readM true s E γr $$ Hsrd
  ihave %hNx := srvKVCoreM_Nx true E γr $$ Hcore
  have hNx' : E.Nx = srvApi.kvNx ρ.rd E.authOn := by rw [hρ, hon]; exact hNx
  ihave #Hauth := srvAuthAt_of_viewsM true s E ρ γr $$ [Hsrv Hsrd]
  · iframe #
  -- the lessor contracts with auth on, at the KV handlers' slot without its `lgMu` reader
  have hS : ⊢ iprop(□ (etcdKVSlot (GF := GF) s E γr -∗ srvLeadTimeReader s ∗ E.RD ∗
      (srvLeadTimeReader s ∗ E.RD -∗ etcdKVSlot s E γr))) := by
    unfold etcdKVSlot
    iintro !> ⟨Hlt, Hm, Hrr, Hrd⟩
    iframe Hlt Hrd
    iintro ⟨Hlt, Hrd⟩
    iframe
  have hG := v3rpc.lessorGrantOkLiveM_server (GF := GF) s E ρ (etcdKVSlot s E γr)
    (fun m => m.2 = W64 0) (fun _ h _ => h) hlg
  have hR := v3rpc.lessorRevokeOkM_server (GF := GF) s E ρ (etcdKVSlot s E γr) hlm
  ihave #HG := hG $$ []
  · rw [hon]; iframe #
    iapply hS
  ihave #HR := hR $$ []
  · rw [hon]; iframe #
    iapply hS
  -- the handlers, through the quota wrapper, at the run's lent form
  ihave #Hg := etcdLeaseGrantHandlerOkMd pl s A lcid lmid E ρ hNx' (etcdKVSlot s E γr) $$ []
  · iframe #
  ihave #Hr := etcdLeaseRevokeHandlerOkMd pl s A lcid lmid E ρ hNx' (etcdKVSlot s E γr) $$ []
  · iframe #
  ihave #Hg' := v3rpc.grpcHandlerOwnOkMd_frame _ _ (srvLgReader s)
    (etcdLeaseGrantSpecOn (srvTLSId s) E ρ (mvcc.api.mvccLeases E.γ)) $$ Hg
  ihave #Hqg := v3rpc.quotaLease_grantHandlerOkMd_of v3rpc.quotaLeaseServer.wp_LeaseGrant
    (etcdLeaseGrantSpecOn (srvTLSId s) E ρ (mvcc.api.mvccLeases E.γ)) ql s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #pl⟩
    (etcdKVSlot s E γr) $$ [Hg']
  · iframe #
  ihave #Hr' := grpcHandlerOkMd_frame _ _ (v3rpc.quotaRd s) (etcdLeaseRevokeSpecOn (srvTLSId s) E ρ) $$ Hr
  ihave #Hqr := v3rpc.quotaLease_revokeHandlerOkMd (etcdLeaseRevokeSpecOn (srvTLSId s) E ρ) ql s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #pl⟩
    iprop(etcdKVSlot s E γr ∗ v3rpc.quotaRd s) $$ [Hq Hr']
  · iframe #
  ihave #Hqg' := grpcHandlerOwnOkMd_slot _ iprop(etcdKVSlot s E γr ∗ v3rpc.quotaRd s)
    iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗ [∗list] R ∈ etcdIcRs s, R) (levelTok 0) _
    (by iintro H
        icases (quotaRd_lent (etcdKVSlot s E γr) s).2 $$ H with ⟨⟨HK, H0⟩, Hq⟩
        iframe)
    (by iintro ⟨⟨HK, Hq⟩, H0⟩; iapply (quotaRd_lent (etcdKVSlot s E γr) s).1; iframe) $$ Hqg
  ihave #Hqr' := etcd_quotaHandler_lent _ (etcdKVSlot s E γr) s _ $$ Hqr
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmg := etcd_leaseGrantMethodOkMd ql _ iprop(etcdKVSlot s E γr ∗ srvBemuReader s) _
    (etcdIcRs s) $$ [Hqg' Ppb Hics]
  · iframe #
  ihave #Hmr := etcd_leaseRevokeMethodOkMd ql _ iprop(etcdKVSlot s E γr ∗ srvBemuReader s) _
    (etcdIcRs s) $$ [Hqr' Ppb Hics]
  · iframe #
  -- the methods at the KV's run slot, then as grpc runs them (the run pools)
  ihave #Hms : iprop(□ [∗list] m ∈ etcdLeaseMethodsOn ql s E ρ,
      grpcMethodOkMd #m.handler m.srv [il, im, iu] (etcdGrpcSlot s E γr) m.spec) $$ []
  · iintro !>
    unfold etcdLeaseMethodsOn etcdGrpcSlot
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbLeaseGrantRequest)
          (Rep := pbLeaseGrantResponse) (@! etcdserverpb._Lease_LeaseGrant_Handler)
          (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #ql) [il, im, iu]
          iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗ [∗list] R ∈ etcdIcRs s, R)
          (etcdLeaseGrantSpecOn (srvTLSId s) E ρ (mvcc.api.mvccLeases E.γ)))
      iexact Hmg
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbLeaseRevokeRequest)
          (Rep := pbLeaseRevokeResponse) (@! etcdserverpb._Lease_LeaseRevoke_Handler)
          (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #ql) [il, im, iu]
          iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗ [∗list] R ∈ etcdIcRs s, R)
          (etcdLeaseRevokeSpecOn (srvTLSId s) E ρ))
      iexact Hmr
    iapply BigSepL.bigSepL_nil.2
    itrivial
  ihave #Hks := etcd_runOks_of_slot [il, im, iu] s E γr HL (etcdLeaseMethodsOn ql s E ρ) $$ [Hms]
  · iframe #
  imod (grpc.serve addr [il, im, iu] regs etcdTys sms (etcdLeaseMethodsOn ql s E ρ)
    (by
      intro x hx
      apply hregs
      simp only [etcdLeaseMethodsOn, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl <;> simp [v3rpc.leaseRegs])
    (by
      intro x hx
      simp only [etcdLeaseMethodsOn, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl <;> simp)) $$ [] with Hrpcs
  · iframe #
  simp only [etcdLeaseMethodsOn, pbLeaseGrantRequestT, pbLeaseGrantResponseT, pbLeaseRevokeRequestT,
    pbLeaseRevokeResponseT]
  icases Hrpcs with ⟨#H1, #H2, -⟩
  imodintro
  iframe #

end proofs

end client
end EtcdGrove
end Perennial
