/-
**etcd's lease reads, served** (the closed lease example, 2026-11-02; `notes/lease-ex-plan.md`).
Lean-first (no Rocq counterpart).

The `*quotaLeaseServer`'s `LeaseTimeToLive` and `LeaseLeases` (the embedded `*LeaseServer`'s,
promoted: `v3rpc.quotaLease_ttlHandlerOk`, `quotaLease_leasesHandlerOk`), `LeaseServer`'s (the
server's call, then the header filled; linked over the contract `v3rpc.raftLeaseRead`), meet the
client's specs `etcdLeaseTTLSpec`/`etcdLeaseLeasesSpecAny` (`InvLeaseRead.lean`), as the grant's and
revoke's meet theirs (`Results.lean`, `etcd_leaseGrantHandlerOk`):

* `etcd_leaseTTLHandlerOk`: the handler's answer (`leaseTTLOut`) is about the asked lease (its
  `ID`, the server's or the handler's not-found reply), its header persisted;
* `etcd_leaseLeasesHandlerOk`: the handler's listing is the lessor's IDs at some index
  (`leaseIdsAt`: no ID twice), or empty;
* `etcd_leaseTTLMethodOk`, `etcd_leaseLeasesMethodOk`: as grpc runs them (the generated handlers,
  under the interceptors); `etcdLeaseReadMethods`/`etcdLeaseReadRegs`: the two methods, registered.

Both handlers run at the slot `S ∗ A.revR` of the contract (`raftLeaseRead_server`'s `S := E.RD ∗
levelTok 0`, `A.revR` the store's reader), with the lower bounds `0` of the auth store and the
lessor's history (`grpcHandlerOk_slot` rearranges a run's slot into it).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PerTypeLease
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead
public import Proof.go_etcd_io.etcd.client.v3.LeaseSpecs
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseTimeToLive_Handler
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseLeases_Handler

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section slot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A service method meeting `Spec` with `S` meets it with any slot `S'` that holds `S` and
gives it back** (`grpcHandlerOk_frame`'s, through the entailments `S' ⊢ S ∗ F`, `S ∗ F ⊢ S'`). -/
theorem grpcHandlerOk_slot {Req Rep : ProtoMsg GF} (h : val) (S S' F : IProp GF)
    (Spec : GrpcSpec Req Rep) (h1 : S' ⊢ S ∗ F) (h2 : S ∗ F ⊢ S') :
    grpcHandlerOk h S Spec ⊢ grpcHandlerOk h S' Spec := by
  iintro #Hh
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS', #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  ihave ⟨HS, HF⟩ := h1 $$ HS'
  iapply Hh $$ %m %Φ %ci %cd %r [HS HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe Hres
  iapply h2
  iframe

end slot

section served
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **etcd's `LeaseTimeToLive` handler meets etcd's `LeaseTimeToLive` spec** (`grpcHandlerOk`),
over the lease-read contract at the run resource `S` and the revision reader `A.revR`, at the lower
bounds `n` (the auth store) and `m` (the lessor's history): `LeaseServer.LeaseTimeToLive`'s answer,
persisted, is the reply's message, about the asked lease. -/
theorem etcd_leaseTTLHandlerOk (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γl : GName) (S : IProp GF) (n m : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLeaseRead s E γl S A.revR ∗
        auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ⊢
      grpcHandlerOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseTimeToLive")
        iprop(S ∗ A.revR) etcdLeaseTTLSpec := by
  iintro ⟨#Pv, #Hat, #HL, #Hn, #Hm⟩
  unfold grpcHandlerOk
  iintro %req %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hrev⟩, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  rw [show (pbLeaseTimeToLiveRequest (GF := GF)).recv r req =
      iprop(∃ v : etcdserverpb.LeaseTimeToLiveRequest, r ↦□ v ∗ ⌜(v.ID', v.Keys') = req⌝) from rfl]
  icases Hr with ⟨%v, #Hv, %Hvm⟩
  iapply wp_fupd
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc
  ihave #Hnetc := netCtxOk_of_runCtx ci $$ Hrc
  ihave #Hcausec := ctxCauseOk_of_runCtx ci $$ Hrc
  ihave ⟨%tok, #HtokC0⟩ := auth.ctxToken_of_libCtxOk ci $$ Hlibc
  ihave #HtokC : iprop(□ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ci) tok)) $$ []
  · iintro !> -; iexact HtokC0
  iapply (v3rpc.LeaseServer.wp_LeaseTimeToLive lp s A cid mid E γl S ci cd tok r DFrac.discard v n m)
    $$ [HS Hrev]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hrev, -, Hout, #HSe⟩
  iunfold v3rpc.leaseTTLOut at Hout
  icases Hout with (⟨%Hok, %w, Hw, %Hid, Hh, -⟩ | %Herr)
  · ihave %Hnn := typedPointsto_not_null $$ Hw
    iunfold v3rpc.leaseHdrDone at Hh
    icases Hh with ⟨Hfd, %dq, %rv, Hrv⟩
    iunfold v3rpc.hdrFilled at Hfd
    icases Hfd with ⟨%Hhn, %t, %ld, Hcid, Hmid, Ht, Hl⟩
    ipersist Hcid
    ipersist Hmid
    ipersist Ht
    ipersist Hl
    ipersist Hrv
    iStructNamedSuffix Hw "_f"
    ipersist Header_f
    ipersist ID_f
    ipersist TTL_f
    ipersist GrantedTTL_f
    ipersist Keys_f
    imodintro
    iapply HΨ
    iframe HS Hrev HSe
    iintro -
    iexists (LeaseTTLRespM.mk (HdrM.mk cid mid rv t ld) w.ID' w.TTL' w.GrantedTTL')
    isplitl []
    · simp only [pbLeaseTimeToLiveResponse]
      unfold leaseTTLRespMsg hdrFull
      isplitl []
      · ipureintro; exact Hnn
      iexists w.Header', w.Keys'
      iframe #
      ipureintro; exact Hhn
    · iunfold etcdLeaseTTLSpec at Hspec
      iapply Hspec
      ipureintro
      simp only
      rw [Hid, ← Hvm]
  · imodintro
    iapply HΨ
    iframe HS Hrev HSe
    iintro %Hnil
    exact absurd Hnil Herr.2

/-- A listed `*LeaseStatus` (owned, `leasesListIs`'s), its `ID` made read-only (the wire's
`leaseLeasesRespMsg`). -/
theorem leaseStatus_persist (p : Loc) (ids : List w64) (k : Nat) :
    iprop(∃ (st : etcdserverpb.LeaseStatus) (id : w64), ⌜ids[k]? = some id ∧ st.ID' = id⌝ ∗
        p ↦ st) ⊢@{IProp GF}
      |==> ∃ id : w64, ⌜ids[k]? = some id⌝ ∗
        structFieldRef etcdserverpb.LeaseStatus go!"ID" p ↦□ id := by
  iintro ⟨%st, %id, %H, Hp⟩
  obtain ⟨H1, H2⟩ := H
  subst H2
  iStructNamedSuffix Hp "_f"
  ipersist ID_f
  imodintro
  iexists st.ID'
  iframe #
  ipureintro; exact H1

/-- **etcd's `LeaseLeases` handler meets etcd's `LeaseLeases` spec** (as
`etcd_leaseTTLHandlerOk`): the reply lists the lessor's IDs at some index of its history, or
none. -/
theorem etcd_leaseLeasesHandlerOk (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γl : GName) (S : IProp GF) (n m : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLeaseRead s E γl S A.revR ∗
        auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ⊢
      grpcHandlerOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseLeases")
        iprop(S ∗ A.revR) etcdLeaseLeasesSpecAny := by
  iintro ⟨#Pv, #Hat, #HL, #Hn, #Hm⟩
  unfold grpcHandlerOk
  iintro %req %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hrev⟩, #Hctx, #Hrc, -, Hspec⟩ HΨ
  iapply wp_fupd
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc
  ihave ⟨%tok, #HtokC0⟩ := auth.ctxToken_of_libCtxOk ci $$ Hlibc
  ihave #HtokC : iprop(□ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ci) tok)) $$ []
  · iintro !> -; iexact HtokC0
  iapply (v3rpc.LeaseServer.wp_LeaseLeases lp s A cid mid E γl S ci cd tok r n m) $$ [HS Hrev]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hrev, Hout, #HSe⟩
  iunfold v3rpc.leaseLeasesOut at Hout
  icases Hout with (⟨%Hok, %w, Hw, Hres⟩ | %Herr)
  · ihave %Hnn := typedPointsto_not_null $$ Hw
    iStructNamedSuffix Hw "_f"
    ipersist Header_f
    ipersist Leases_f
    icases Hres with ⟨%i, %ids, %Hmi, #Hids, Hh, Hl, -⟩
    ihave %Hnd := lease.leaseIdsAt_nodup γl i ids $$ Hids
    iunfold v3rpc.leasesHdrDone at Hh
    icases Hh with ⟨Hfd, %dq, %rv, %log, Hrv, -, -⟩
    iunfold v3rpc.hdrFilled at Hfd
    icases Hfd with ⟨%Hhn, %t, %ld, Hcid, Hmid, Ht, Hld⟩
    ipersist Hcid
    ipersist Hmid
    ipersist Ht
    ipersist Hld
    ipersist Hrv
    iunfold leasesListIs at Hl
    icases Hl with ⟨%ps, Hsl, %Hlen, Hps⟩
    ipersist Hsl
    ihave Hps' : |==> [∗list] k ↦ x ∈ ps, iprop(∃ id : w64, ⌜ids[k]? = some id⌝ ∗
        structFieldRef etcdserverpb.LeaseStatus go!"ID" x ↦□ id) $$ [Hps]
    · iapply BigSepL.bigSepL_bupd
      iapply (BigSepL.bigSepL_mono (fun {k x} _ => leaseStatus_persist x ids k)) $$ Hps
    imod Hps' with #Hps'
    imodintro
    iapply HΨ
    iframe HS Hrev HSe
    iintro -
    iexists (LeaseLeasesRespM.mk (HdrM.mk cid mid rv t ld) ids)
    isplitl []
    · simp only [pbLeaseLeasesResponse]
      unfold leaseLeasesRespMsg hdrFull
      isplitl []
      · ipureintro; exact Hnn
      iexists w.Header', w.Leases', ps
      iframe #
      ipureintro; exact ⟨Hhn, Hlen⟩
    · iunfold etcdLeaseLeasesSpecAny at Hspec
      iapply Hspec
      ipureintro; exact Hnd
  · imodintro
    iapply HΨ
    iframe HS Hrev HSe
    iintro %Hnil
    exact absurd Hnil Herr.2.1

/-- The lease reads' requests at a pointer: the learner check reads nothing of them. -/
theorem leaseTTLReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseTimeToLiveRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.LeaseTimeToLiveRequest.ty, etcdserverpb.RangeRequest.ty])

theorem leaseLeasesReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseLeasesRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.LeaseLeasesRequest.ty, etcdserverpb.RangeRequest.ty])

/-- **etcd's `LeaseTimeToLive`, as grpc runs it, at a metadata-indexed spec** (auth-lease S4; as
`etcd_leaseRevokeMethodOkMd`). -/
theorem etcd_leaseTTLMethodOkMd (q : Loc)
    (Spec : GrpcSpecMd (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOkMd (q @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseTimeToLive")
        iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._Lease_LeaseTimeToLive_Handler)
        (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.LeaseTimeToLiveRequest) -∗
      (pbLeaseTimeToLiveRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbLeaseTimeToLiveRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbLeaseTimeToLiveRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk
        (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseTimeToLiveRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply leaseTTLReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__Lease_LeaseTimeToLive_Handler pbLeaseTimeToLiveRequest
    pbLeaseTimeToLiveResponse Spec ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ Ψe ci cd dec ui rfl rfl v3rpc.ServerMethodSets.lease_impl)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `LeaseLeases`, as grpc runs it, at a metadata-indexed spec** (as
`etcd_leaseTTLMethodOkMd`). -/
theorem etcd_leaseLeasesMethodOkMd (q : Loc)
    (Spec : GrpcSpecMd (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOkMd (q @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseLeases")
        iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._Lease_LeaseLeases_Handler)
        (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.LeaseLeasesRequest) -∗
      (pbLeaseLeasesRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbLeaseLeasesRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbLeaseLeasesRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk
        (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseLeasesRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply leaseLeasesReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__Lease_LeaseLeases_Handler pbLeaseLeasesRequest
    pbLeaseLeasesResponse Spec ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ Ψe ci cd dec ui rfl rfl v3rpc.ServerMethodSets.lease_impl)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `LeaseTimeToLive`, as grpc runs it** (as `etcd_leaseGrantMethodOk`). -/
theorem etcd_leaseTTLMethodOk (q : Loc)
    (Spec : GrpcSpec (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseTimeToLive")
        iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Lease_LeaseTimeToLive_Handler)
        (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  iapply (grpcMethodOk_md _ _ _ _ _).2
  iapply etcd_leaseTTLMethodOkMd
  iframe #
  iapply (grpcHandlerOk_md _ _ _).1
  iexact Hh

/-- **etcd's `LeaseLeases`, as grpc runs it** (as `etcd_leaseGrantMethodOk`). -/
theorem etcd_leaseLeasesMethodOk (q : Loc)
    (Spec : GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseLeases")
        iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Lease_LeaseLeases_Handler)
        (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  iapply (grpcMethodOk_md _ _ _ _ _).2
  iapply etcd_leaseLeasesMethodOkMd
  iframe #
  iapply (grpcHandlerOk_md _ _ _).1
  iexact Hh

/-- **etcd's lease reads** as registered: `LeaseTimeToLive` and `LeaseLeases`, the generated
handlers of `Lease_ServiceDesc` with the `*quotaLeaseServer` `q`, with etcd's specs. -/
def etcdLeaseReadMethods (q : Loc) : List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.Lease/LeaseTimeToLive", pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT,
     GrpcSpec.md etcdLeaseTTLSpec, (functions etcdserverpb._Lease_LeaseTimeToLive_Handler []),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseTimeToLiveRequestT_reg, pbLeaseTimeToLiveResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Lease/LeaseLeases", pbLeaseLeasesRequestT, pbLeaseLeasesResponseT,
     GrpcSpec.md etcdLeaseLeasesSpecAny, (functions etcdserverpb._Lease_LeaseLeases_Handler []),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseLeasesRequestT_reg, pbLeaseLeasesResponseT_reg⟩]

/-- **The lease reads as grpc runs them, at the KV's run slot with the level-0 token**
(`etcdGrpcSlot s E γr ∗ levelTok 0`, the one slot of a server serving both: a run's bundle
`srvRunBundle`, by `etcdGrpcSlot_bundle`): the handler meets at
the contract's slot (`raftLeaseRead_server`'s `E.RD ∗ levelTok 0`, the store's reader `A.revR`)
rearranged (`grpcHandlerOk_slot`), promoted through the `*quotaLeaseServer` `q`, under the
interceptors. -/
theorem etcd_leaseReadMethodsOk (lp q s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γr : ReadNames) (γl : GName) (il im iu : GoFunc)
    (hA : A.revR = mvcc.api.mvccReaders E.γ 1) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗
        v3rpc.raftLeaseRead s E γl iprop(E.RD ∗ levelTok 0) (mvcc.api.mvccReaders E.γ 1) ∗
        auth.authPubLbM E.authMode 0 ∗ lease.lessorLb γl 0 ∗
        v3rpc.quotaLeaseServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu (levelTok 0) v3rpc.learnerReqOk ⊢
      [∗list] m ∈ etcdLeaseReadMethods q,
        grpcMethodOkMd #m.handler m.srv [il, im, iu] (etcdGrpcSlot s E γr) m.spec := by
  iintro ⟨#Pv, #Hat, #HL0, #Hn, #Hm, #Hq, #Hil, #Him, #Hiu⟩
  ihave #HL : v3rpc.raftLeaseRead s E γl iprop(E.RD ∗ levelTok 0) A.revR $$ []
  · rw [hA]; iexact HL0
  -- the handler's slot: the KV slot, the quota check's `bemu` reader and the level-0 token, with the
  -- interceptors' lent resources
  have h1 : iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗
        [∗list] R ∈ etcdIcRs s, R) ⊢
      iprop(((E.RD ∗ levelTok 0) ∗ A.revR) ∗
        (srvLeadTimeReader s ∗ srvReadReader s γr ∗ srvBemuReader s ∗
          srvLgReader s)) := by
    rw [hA]; unfold etcdKVSlot
    iintro ⟨⟨⟨Hlt, Hst, Hrr, Hrd⟩, Hbe⟩, HRs⟩
    icases (etcdIcRs_eq s).1 $$ HRs with ⟨Hlg, Ht⟩
    iframe
  have h2 : iprop(((E.RD ∗ levelTok 0) ∗ A.revR) ∗
        (srvLeadTimeReader s ∗ srvReadReader s γr ∗ srvBemuReader s ∗
          srvLgReader s)) ⊢
      iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗
        [∗list] R ∈ etcdIcRs s, R) := by
    rw [hA]; unfold etcdKVSlot
    iintro ⟨⟨⟨Hrd, Ht⟩, Hst⟩, Hlt, Hrr, Hbe, Hlg⟩
    iframe
    iapply (etcdIcRs_eq s).2
    iframe
  have h3 : (etcdGrpcSlot s E γr) ⊢
      iprop(((etcdKVSlot s E γr ∗ srvBemuReader s) ∗
        [∗list] R ∈ etcdIcRs s, R) ∗ True) := by
    unfold etcdGrpcSlot
    iintro ⟨Hrs, HRs⟩
    iframe
  have h4 : iprop(((etcdKVSlot s E γr ∗ srvBemuReader s) ∗
        [∗list] R ∈ etcdIcRs s, R) ∗ True) ⊢ (etcdGrpcSlot s E γr) := by
    unfold etcdGrpcSlot
    iintro ⟨⟨Hrs, HRs⟩, -⟩
    iframe
  ihave #Ht := etcd_leaseTTLHandlerOk lp s A cid mid E γl iprop(E.RD ∗ levelTok 0) 0 0 $$ []
  · iframe #
  ihave #Hl := etcd_leaseLeasesHandlerOk lp s A cid mid E γl iprop(E.RD ∗ levelTok 0) 0 0 $$ []
  · iframe #
  ihave #Ht' := grpcHandlerOk_slot _ _ _ _ etcdLeaseTTLSpec h1 h2 $$ Ht
  ihave #Hl' := grpcHandlerOk_slot _ _ _ _ etcdLeaseLeasesSpecAny h1 h2 $$ Hl
  ihave #Hqt := v3rpc.quotaLease_ttlHandlerOk etcdLeaseTTLSpec q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗ [∗list] R ∈ etcdIcRs s, R)
    $$ [Hq Ht']
  · iframe #
  ihave #Hql := v3rpc.quotaLease_leasesHandlerOk etcdLeaseLeasesSpecAny q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗ [∗list] R ∈ etcdIcRs s, R)
    $$ [Hq Hl']
  · iframe #
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmt := etcd_leaseTTLMethodOk q _ iprop(etcdKVSlot s E γr ∗ srvBemuReader s)
    _ (etcdIcRs s) $$ [Hqt Ppb Hics]
  · iframe #
  ihave #Hml := etcd_leaseLeasesMethodOk q _ iprop(etcdKVSlot s E γr ∗ srvBemuReader s)
    _ (etcdIcRs s) $$ [Hql Ppb Hics]
  · iframe #
  ihave #Hmt' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmt
  ihave #Hml' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hml
  ihave #Hmt'' := grpcMethodOkMd_slot _ _ _ _ (etcdGrpcSlot s E γr) _ _ h3 h4 $$ Hmt'
  ihave #Hml'' := grpcMethodOkMd_slot _ _ _ _ (etcdGrpcSlot s E γr) _ _ h3 h4 $$ Hml'
  unfold etcdLeaseReadMethods
  iapply bigSepL_cons_intro'
  isplitl []
  · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbLeaseTimeToLiveRequest)
          (Rep := pbLeaseTimeToLiveResponse) (@! etcdserverpb._Lease_LeaseTimeToLive_Handler)
          (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q) [il, im, iu]
          (etcdGrpcSlot s E γr) (GrpcSpec.md etcdLeaseTTLSpec))
    iexact Hmt''
  iapply bigSepL_cons_intro'
  isplitl []
  · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbLeaseLeasesRequest)
          (Rep := pbLeaseLeasesResponse) (@! etcdserverpb._Lease_LeaseLeases_Handler)
          (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q) [il, im, iu]
          (etcdGrpcSlot s E γr) (GrpcSpec.md etcdLeaseLeasesSpecAny))
    iexact Hml''
  iapply BigSepL.bigSepL_nil.2
  itrivial


/-- **etcd's `LeaseTimeToLive` handler meets `etcdLeaseTTLSpecMd`** (`grpcHandlerOkMd`; auth-lease S4,
Freeze §4.1, any auth mode), over the lease-read contract at the run resource `S` and the revision
reader `A.revR`: the call is made at the caller's lower bounds `n`, `m`; `LeaseServer.LeaseTimeToLive`'s
answer (`leaseTTLOut`) carries the check relative to `n` on both arms (Freeze §10 T1), at the request
context's token, which is the attempt's metadata's (`auth.ctxToken_of_ctxInMD`). -/
theorem etcdLeaseTTLHandlerOkMd (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γl : GName) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLeaseRead s E γl S A.revR ⊢
      grpcHandlerOkMd (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseTimeToLive")
        iprop(S ∗ A.revR) (etcdLeaseTTLSpecMd s E γl) := by
  iintro ⟨#Pv, #Hat, #HL⟩
  unfold grpcHandlerOkMd grpcSpecAt etcdLeaseTTLSpecMd
  iintro %req %Φ %Ψe %ci %cd %r !> %Ψ ⟨⟨HS, Hrev⟩, #Hctx, #Hrc, #Hr, %md, #Hmd, ⟨#HΨe, %n, %m, #Hn, #Hm, Hk⟩⟩ HΨ
  ihave #HtokC0 := auth.ctxToken_of_ctxInMD ci md $$ Hmd
  ihave #HtokC : iprop(□ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ci) (auth.mdTokenOf md))) $$ []
  · iintro !> -; iexact HtokC0
  rw [show (pbLeaseTimeToLiveRequest (GF := GF)).recv r req =
      iprop(∃ v : etcdserverpb.LeaseTimeToLiveRequest, r ↦□ v ∗ ⌜(v.ID', v.Keys') = req⌝) from rfl]
  icases Hr with ⟨%v, #Hv, %Hvm⟩
  subst Hvm
  iapply wp_fupd
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc
  ihave #Hnetc := netCtxOk_of_runCtx ci $$ Hrc
  ihave #Hcausec := ctxCauseOk_of_runCtx ci $$ Hrc
  iapply (v3rpc.LeaseServer.wp_LeaseTimeToLive lp s A cid mid E γl S ci cd (auth.mdTokenOf md) r DFrac.discard v n m)
    $$ [HS Hrev]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hrev, -, Hout, #HSe⟩
  iunfold v3rpc.leaseTTLOut at Hout
  icases Hout with (⟨%Hok, %w, Hw, %Hid, Hh, #Hauth, #Hchk, Harm⟩ | %Herr)
  · ihave #Hf : □ (leaseTTLRow s γl -∗
        (∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i v.ID' w.GrantedTTL') ∨
        lease.leaseAbsentFrom γl m v.ID') $$ [Harm]
    · icases Harm with (#Hf | ⟨-, #Hnf⟩)
      · iexact Hf
      · iintro !> #Hrow
        iright
        iapply Hnf $$ Hrow
    ihave %Hnn := typedPointsto_not_null $$ Hw
    iunfold v3rpc.leaseHdrDone at Hh
    icases Hh with ⟨Hfd, %dq, %rv, Hrv⟩
    iunfold v3rpc.hdrFilled at Hfd
    icases Hfd with ⟨%Hhn, %t, %ld, Hcid, Hmid, Ht, Hl⟩
    ipersist Hcid
    ipersist Hmid
    ipersist Ht
    ipersist Hl
    ipersist Hrv
    iStructNamedSuffix Hw "_f"
    ipersist Header_f
    ipersist ID_f
    ipersist TTL_f
    ipersist GrantedTTL_f
    ipersist Keys_f
    imodintro
    iapply HΨ
    iframe HS Hrev HSe
    isplitl
    · iintro -
      iexists (LeaseTTLRespM.mk (HdrM.mk cid mid rv t ld) w.ID' w.TTL' w.GrantedTTL')
      isplitl []
      · simp only [pbLeaseTimeToLiveResponse]
        unfold leaseTTLRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hnn
        iexists w.Header', w.Keys'
        iframe #
        ipureintro; exact Hhn
      · have hid' : (LeaseTTLRespM.mk (HdrM.mk cid mid rv t ld) w.ID' w.TTL' w.GrantedTTL').id =
            (v.ID', v.Keys').1 := by
          simp only; exact Hid
        iapply Hk $$ %(LeaseTTLRespM.mk (HdrM.mk cid mid rv t ld) w.ID' w.TTL' w.GrantedTTL') %hid'
          [] []
        · simp only
          rw [Hid]
          iexact Hf
        · iexact Hchk
    · iapply (handlerErrOut_allSrv _ err) $$ HΨe HSe
  · imodintro
    iapply HΨ
    iframe HS Hrev HSe
    isplitl
    · iintro %Hnil
      exact absurd Hnil Herr.2
    · iapply (handlerErrOut_allSrv _ err) $$ HΨe HSe

/-- **etcd's `LeaseLeases` handler meets `etcdLeaseLeasesSpecMd`** (`grpcHandlerOkMd`; auth-lease S4,
Freeze §4.2, any auth mode; as `etcdLeaseTTLHandlerOkMd`): the listing is the lessor's ids at an index
`≥ m` (`leaseLeasesOut`'s; its empty-listing arm gone, Freeze §4.4 F4), with each lease's verdict at
the attempt's token. -/
theorem etcdLeaseLeasesHandlerOkMd (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γl : GName) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLeaseRead s E γl S A.revR ⊢
      grpcHandlerOkMd (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseLeases")
        iprop(S ∗ A.revR) (etcdLeaseLeasesSpecMd s E γl) := by
  iintro ⟨#Pv, #Hat, #HL⟩
  unfold grpcHandlerOkMd grpcSpecAt etcdLeaseLeasesSpecMd
  iintro %req %Φ %Ψe %ci %cd %r !> %Ψ ⟨⟨HS, Hrev⟩, #Hctx, #Hrc, -, %md, #Hmd, ⟨#HΨe, %n, %m, #Hn, #Hm, Hk⟩⟩ HΨ
  ihave #HtokC0 := auth.ctxToken_of_ctxInMD ci md $$ Hmd
  ihave #HtokC : iprop(□ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ci) (auth.mdTokenOf md))) $$ []
  · iintro !> -; iexact HtokC0
  iapply wp_fupd
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc
  iapply (v3rpc.LeaseServer.wp_LeaseLeases lp s A cid mid E γl S ci cd (auth.mdTokenOf md) r n m) $$ [HS Hrev]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hrev, Hout, #HSe⟩
  iunfold v3rpc.leaseLeasesOut at Hout
  icases Hout with (⟨%Hok, %w, Hw, %i, %ids, %Hmi, #Hids, Hh, Hl, #Hchk⟩ | %Herr)
  · ihave %Hnn := typedPointsto_not_null $$ Hw
    iStructNamedSuffix Hw "_f"
    ipersist Header_f
    ipersist Leases_f
    ihave %Hnd := lease.leaseIdsAt_nodup γl i ids $$ Hids
    iunfold v3rpc.leasesHdrDone at Hh
    icases Hh with ⟨Hfd, %dq, %rv, %log, Hrv, -, -⟩
    iunfold v3rpc.hdrFilled at Hfd
    icases Hfd with ⟨%Hhn, %t, %ld, Hcid, Hmid, Ht, Hld⟩
    ipersist Hcid
    ipersist Hmid
    ipersist Ht
    ipersist Hld
    ipersist Hrv
    iunfold leasesListIs at Hl
    icases Hl with ⟨%ps, Hsl, %Hlen, Hps⟩
    ipersist Hsl
    ihave Hps' : |==> [∗list] k ↦ x ∈ ps, iprop(∃ id : w64, ⌜ids[k]? = some id⌝ ∗
        structFieldRef etcdserverpb.LeaseStatus go!"ID" x ↦□ id) $$ [Hps]
    · iapply BigSepL.bigSepL_bupd
      iapply (BigSepL.bigSepL_mono (fun {k x} _ => leaseStatus_persist x ids k)) $$ Hps
    imod Hps' with #Hps'
    imodintro
    iapply HΨ
    iframe HS Hrev HSe
    isplitl
    · iintro -
      iexists (LeaseLeasesRespM.mk (HdrM.mk cid mid rv t ld) ids)
      isplitl []
      · simp only [pbLeaseLeasesResponse]
        unfold leaseLeasesRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hnn
        iexists w.Header', w.Leases', ps
        iframe #
        ipureintro; exact ⟨Hhn, Hlen⟩
      · iapply Hk $$ %(LeaseLeasesRespM.mk (HdrM.mk cid mid rv t ld) ids) %Hnd
        iexists i
        iframe Hids
        isplitr
        · ipureintro; exact Hmi
        iexact Hchk
    · iapply (handlerErrOut_allSrv _ err) $$ HΨe HSe
  · imodintro
    iapply HΨ
    iframe HS Hrev HSe
    isplitl
    · iintro %Hnil
      exact absurd Hnil Herr.2.1
    · iapply (handlerErrOut_allSrv _ err) $$ HΨe HSe

/-- **etcd's lease reads at the metadata-indexed specs** as registered (auth-lease S4, Freeze §4):
`LeaseTimeToLive` and `LeaseLeases`, the generated handlers of `Lease_ServiceDesc` with the
`*quotaLeaseServer` `q`, at `etcdLeaseTTLSpecMd`/`etcdLeaseLeasesSpecMd` over the server `s` and the
lessor `γl`. -/
def etcdLeaseReadMethodsMd (q s : Loc) (E : apply.AEnv GF) (γl : GName) : List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.Lease/LeaseTimeToLive", pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT,
     etcdLeaseTTLSpecMd s E γl, (functions etcdserverpb._Lease_LeaseTimeToLive_Handler []),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseTimeToLiveRequestT_reg, pbLeaseTimeToLiveResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Lease/LeaseLeases", pbLeaseLeasesRequestT, pbLeaseLeasesResponseT,
     etcdLeaseLeasesSpecMd s E γl, (functions etcdserverpb._Lease_LeaseLeases_Handler []),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseLeasesRequestT_reg, pbLeaseLeasesResponseT_reg⟩]

/-- **The lease reads at the metadata-indexed specs as grpc runs them, at the KV's run slot with the
level-0 token** (auth-lease S4; as `etcd_leaseReadMethodsOk`, without the lower bounds, which the
specs' callers supply). -/
theorem etcd_leaseReadMethodsOkMd (lp q s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γr : ReadNames) (γl : GName) (il im iu : GoFunc)
    (hA : A.revR = mvcc.api.mvccReaders E.γ 1) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗
        v3rpc.raftLeaseRead s E γl iprop(E.RD ∗ levelTok 0) (mvcc.api.mvccReaders E.γ 1) ∗
        v3rpc.quotaLeaseServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu (levelTok 0) v3rpc.learnerReqOk ⊢
      [∗list] m ∈ etcdLeaseReadMethodsMd q s E γl,
        grpcMethodOkMd #m.handler m.srv [il, im, iu] (etcdGrpcSlot s E γr) m.spec := by
  iintro ⟨#Pv, #Hat, #HL0, #Hq, #Hil, #Him, #Hiu⟩
  ihave #HL : v3rpc.raftLeaseRead s E γl iprop(E.RD ∗ levelTok 0) A.revR $$ []
  · rw [hA]; iexact HL0
  have h1 : iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗
        [∗list] R ∈ etcdIcRs s, R) ⊢
      iprop(((E.RD ∗ levelTok 0) ∗ A.revR) ∗
        (srvLeadTimeReader s ∗ srvReadReader s γr ∗ srvBemuReader s ∗
          srvLgReader s)) := by
    rw [hA]; unfold etcdKVSlot
    iintro ⟨⟨⟨Hlt, Hst, Hrr, Hrd⟩, Hbe⟩, HRs⟩
    icases (etcdIcRs_eq s).1 $$ HRs with ⟨Hlg, Ht⟩
    iframe
  have h2 : iprop(((E.RD ∗ levelTok 0) ∗ A.revR) ∗
        (srvLeadTimeReader s ∗ srvReadReader s γr ∗ srvBemuReader s ∗
          srvLgReader s)) ⊢
      iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗
        [∗list] R ∈ etcdIcRs s, R) := by
    rw [hA]; unfold etcdKVSlot
    iintro ⟨⟨⟨Hrd, Ht⟩, Hst⟩, Hlt, Hrr, Hbe, Hlg⟩
    iframe
    iapply (etcdIcRs_eq s).2
    iframe
  have h3 : (etcdGrpcSlot s E γr) ⊢
      iprop(((etcdKVSlot s E γr ∗ srvBemuReader s) ∗
        [∗list] R ∈ etcdIcRs s, R) ∗ True) := by
    unfold etcdGrpcSlot
    iintro ⟨Hrs, HRs⟩
    iframe
  have h4 : iprop(((etcdKVSlot s E γr ∗ srvBemuReader s) ∗
        [∗list] R ∈ etcdIcRs s, R) ∗ True) ⊢ (etcdGrpcSlot s E γr) := by
    unfold etcdGrpcSlot
    iintro ⟨⟨Hrs, HRs⟩, -⟩
    iframe
  ihave #Ht := etcdLeaseTTLHandlerOkMd lp s A cid mid E γl iprop(E.RD ∗ levelTok 0) $$ []
  · iframe #
  ihave #Hl := etcdLeaseLeasesHandlerOkMd lp s A cid mid E γl iprop(E.RD ∗ levelTok 0) $$ []
  · iframe #
  ihave #Ht' := grpcHandlerOkMd_slot _ _ _ _ (etcdLeaseTTLSpecMd s E γl) h1 h2 $$ Ht
  ihave #Hl' := grpcHandlerOkMd_slot _ _ _ _ (etcdLeaseLeasesSpecMd s E γl) h1 h2 $$ Hl
  ihave #Hqt := v3rpc.quotaLease_ttlHandlerOkMd (etcdLeaseTTLSpecMd s E γl) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗ [∗list] R ∈ etcdIcRs s, R)
    $$ [Hq Ht']
  · iframe #
  ihave #Hql := v3rpc.quotaLease_leasesHandlerOkMd (etcdLeaseLeasesSpecMd s E γl) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop((etcdKVSlot s E γr ∗ srvBemuReader s) ∗ [∗list] R ∈ etcdIcRs s, R)
    $$ [Hq Hl']
  · iframe #
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmt := etcd_leaseTTLMethodOkMd q _ iprop(etcdKVSlot s E γr ∗ srvBemuReader s)
    _ (etcdIcRs s) $$ [Hqt Ppb Hics]
  · iframe #
  ihave #Hml := etcd_leaseLeasesMethodOkMd q _ iprop(etcdKVSlot s E γr ∗ srvBemuReader s)
    _ (etcdIcRs s) $$ [Hql Ppb Hics]
  · iframe #
  ihave #Hmt'' := grpcMethodOkMd_slot _ _ _ _ (etcdGrpcSlot s E γr) _ _ h3 h4 $$ Hmt
  ihave #Hml'' := grpcMethodOkMd_slot _ _ _ _ (etcdGrpcSlot s E γr) _ _ h3 h4 $$ Hml
  unfold etcdLeaseReadMethodsMd
  iapply bigSepL_cons_intro'
  isplitl []
  · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbLeaseTimeToLiveRequest)
          (Rep := pbLeaseTimeToLiveResponse) (@! etcdserverpb._Lease_LeaseTimeToLive_Handler)
          (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q) [il, im, iu]
          (etcdGrpcSlot s E γr) (etcdLeaseTTLSpecMd s E γl))
    iexact Hmt''
  iapply bigSepL_cons_intro'
  isplitl []
  · change Iris.ProofMode.Entails' _ (grpcMethodOkMd (Req := pbLeaseLeasesRequest)
          (Rep := pbLeaseLeasesResponse) (@! etcdserverpb._Lease_LeaseLeases_Handler)
          (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q) [il, im, iu]
          (etcdGrpcSlot s E γr) (etcdLeaseLeasesSpecMd s E γl))
    iexact Hml''
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- **etcd's lease reads served at the metadata-indexed specs** (`etcd_lease_read_served`; auth-lease
S4, Freeze §4.3, rev 2's R2): the read handlers registered at `etcdLeaseTTLSpecMd`/`etcdLeaseLeasesSpecMd`,
at any auth mode (nothing in the handler path uses the mode) and at the lease-read contract's lessor `γl`.
The auth-off `etcd_leaseReadMethodsOk`'s specs (`etcdLeaseTTLSpec`, `etcdLeaseLeasesSpecAny`) stay
proved on their own. -/
theorem etcd_lease_read_served (addr : GoString) (ql pl s : Loc) (A : v3rpc.KVAns GF)
    (lcid lmid : w64) (E : apply.AEnv GF) (γr : ReadNames) (γl : GName) (il im iu : GoFunc)
    (regs : List (GoString × GoFunc × GoInterface)) (γ : GName)
    (hA : A.revR = mvcc.api.mvccReaders E.γ 1)
    (hregs : ∀ x ∈ v3rpc.leaseRegs ql, x ∈ regs) (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      v3rpc.quotaLeaseServerAt ql
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #pl⟩ s ∗
      v3rpc.leaseServerAt pl s A lcid lmid ∗
      v3rpc.raftLeaseRead s E γl iprop(E.RD ∗ levelTok 0) (mvcc.api.mvccReaders E.γ 1) ∗
      srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗ srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
      srvInterceptorOk iu (levelTok 0) v3rpc.learnerReqOk ∗
      grpcServerAt addr [il, im, iu] regs γ ∗ srvRevokeBuilt s E ∗ srvRunPool s E γr ⊢
    |={⊤}=> isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseTimeToLive" (etcdLeaseTTLSpecMd s E γl) ∗
      isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpecMd s E γl) := by
  iintro ⟨#Pv, -, #Hq, #Hat, #HL0, #Hil, #Him, #Hiu, #Hsa, #Hb, #Hrpl⟩
  ihave #Hms := etcd_leaseReadMethodsOkMd pl ql s A lcid lmid E γr γl il im iu hA $$ []
  · iframe #
  have h1 : srvRunBundle s E γr ⊢ (etcdGrpcSlot s E γr) ∗ iprop(True) := by
    iintro H
    ihave H := (etcdGrpcSlot_bundle s E γr).1 $$ H
    iframe
  have h2 : (etcdGrpcSlot s E γr) ∗ iprop(True) ⊢ srvRunBundle s E γr := by
    iintro ⟨H, -⟩
    iapply (etcdGrpcSlot_bundle s E γr).2
    iexact H
  ihave #Hks := srvRunOks_of_slot s E γr [il, im, iu] (etcdGrpcSlot s E γr)
      iprop(True) h1 h2 HL (etcdLeaseReadMethodsMd ql s E γl) $$ []
  · iframe #
  imod (grpc.serve addr [il, im, iu] regs (etcdLeaseReadMethodsMd ql s E γl) γ
    (by
      intro x hx
      apply hregs
      simp only [etcdLeaseReadMethodsMd, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl <;> simp [v3rpc.leaseRegs])) $$ [] with Hrpcs
  · iframe #
  simp only [etcdLeaseReadMethodsMd, pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT,
    pbLeaseLeasesRequestT, pbLeaseLeasesResponseT]
  icases Hrpcs with ⟨#H1, #H2, -⟩
  imodintro
  iframe #

end served

end client
end EtcdGrove
end Perennial
