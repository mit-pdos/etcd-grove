/-
**etcd's lease reads, served** (the closed lease example, 2026-11-02; `notes/lease-ex-plan.md`).
Lean-first (no Rocq counterpart).

The `*quotaLeaseServer`'s `LeaseTimeToLive` and `LeaseLeases` (the embedded `*LeaseServer`'s,
promoted: `v3rpc.quotaLease_ttlHandlerOk`, `quotaLease_leasesHandlerOk`), `LeaseServer`'s (the
server's call, then the header filled; linked over the contract `v3rpc.raftLeaseRead`), meet the
client's specs `etcdLeaseTTLSpec`/`etcdLeaseLeasesSpec` (`InvLeaseRead.lean`), as the grant's and
revoke's meet theirs (`Results.lean`, `etcd_leaseGrantHandlerOk`):

* `etcd_leaseTTLHandlerOk`: the handler's answer (`leaseTTLOut`) is about the asked lease (its
  `ID`, the server's or the handler's not-found reply), its header persisted;
* `etcd_leaseLeasesHandlerOk`: the handler's listing is the lessor's IDs at some index
  (`leaseIdsAt`: no ID twice), or empty;
* `etcd_leaseTTLMethodOk`, `etcd_leaseLeasesMethodOk`: as grpc runs them (the generated handlers,
  under the interceptors); `etcdLeaseReadMethods`/`etcdLeaseReadRegs`: the two methods, registered.

Both handlers run at the slot `S ∗ A.revR` of the contract (`raftLeaseRead_server`'s `S := E.RD ∗
threadTok`, `A.revR` the store's reader), with the lower bounds `0` of the auth store and the
lessor's history (`grpcHandlerOk_slot` rearranges a run's slot into it).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead
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
  iapply (v3rpc.LeaseServer.wp_LeaseTimeToLive lp s A cid mid E γl S ci cd r DFrac.discard v n m)
    $$ [HS Hrev]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hrev, -, Hout⟩
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
    iframe HS Hrev
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
    iframe HS Hrev
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
        iprop(S ∗ A.revR) etcdLeaseLeasesSpec := by
  iintro ⟨#Pv, #Hat, #HL, #Hn, #Hm⟩
  unfold grpcHandlerOk
  iintro %req %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hrev⟩, #Hctx, #Hrc, -, Hspec⟩ HΨ
  iapply wp_fupd
  iapply (v3rpc.LeaseServer.wp_LeaseLeases lp s A cid mid E γl S ci cd r n m) $$ [HS Hrev]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hrev, Hout⟩
  iunfold v3rpc.leaseLeasesOut at Hout
  icases Hout with (⟨%Hok, %w, Hw, Hres⟩ | %Herr)
  · ihave %Hnn := typedPointsto_not_null $$ Hw
    iStructNamedSuffix Hw "_f"
    ipersist Header_f
    ipersist Leases_f
    icases Hres with (⟨%i, %ids, %Hmi, #Hids, Hh, Hl, -⟩ | ⟨Hh, Hl⟩)
    · ihave %Hnd := lease.leaseIdsAt_nodup γl i ids $$ Hids
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
      iframe HS Hrev
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
      · iunfold etcdLeaseLeasesSpec at Hspec
        iapply Hspec
        ipureintro; exact Hnd
    · iunfold v3rpc.leaseHdrDone at Hh
      icases Hh with ⟨Hfd, %dq, %rv, Hrv⟩
      iunfold v3rpc.hdrFilled at Hfd
      icases Hfd with ⟨%Hhn, %t, %ld, Hcid, Hmid, Ht, Hld⟩
      ipersist Hcid
      ipersist Hmid
      ipersist Ht
      ipersist Hld
      ipersist Hrv
      ipersist Hl
      imodintro
      iapply HΨ
      iframe HS Hrev
      iintro -
      iexists (LeaseLeasesRespM.mk (HdrM.mk cid mid rv t ld) [])
      isplitl []
      · simp only [pbLeaseLeasesResponse]
        unfold leaseLeasesRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hnn
        iexists w.Header', w.Leases', []
        iframe #
        isplitl []
        · ipureintro; exact Hhn
        isplitl []
        · ipureintro; rfl
        iapply BigSepL.bigSepL_nil.2
        itrivial
      · iunfold etcdLeaseLeasesSpec at Hspec
        iapply Hspec
        ipureintro; exact List.nodup_nil
  · imodintro
    iapply HΨ
    iframe HS Hrev
    iintro %Hnil
    exact absurd Hnil Herr.2

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

/-- **etcd's `LeaseTimeToLive`, as grpc runs it** (as `etcd_leaseGrantMethodOk`). -/
theorem etcd_leaseTTLMethodOk (q : Loc)
    (Spec : GrpcSpec (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseTimeToLive")
        S Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Lease_LeaseTimeToLive_Handler)
        (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.LeaseTimeToLiveRequest) -∗
      (pbLeaseTimeToLiveRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbLeaseTimeToLiveRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbLeaseTimeToLiveRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk
        (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseTimeToLiveRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply leaseTTLReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__Lease_LeaseTimeToLive_Handler pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse
    Spec ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.ServerMethodSets.lease_impl)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `LeaseLeases`, as grpc runs it** (as `etcd_leaseGrantMethodOk`). -/
theorem etcd_leaseLeasesMethodOk (q : Loc)
    (Spec : GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseLeases")
        S Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Lease_LeaseLeases_Handler)
        (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.LeaseLeasesRequest) -∗
      (pbLeaseLeasesRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbLeaseLeasesRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbLeaseLeasesRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk
        (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseLeasesRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply leaseLeasesReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__Lease_LeaseLeases_Handler pbLeaseLeasesRequest pbLeaseLeasesResponse
    Spec ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.ServerMethodSets.lease_impl)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's lease reads** as registered: `LeaseTimeToLive` and `LeaseLeases`, the generated
handlers of `Lease_ServiceDesc` with the `*quotaLeaseServer` `q`, with etcd's specs. -/
def etcdLeaseReadMethods (q : Loc) : List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.Lease/LeaseTimeToLive", pbLeaseTimeToLiveRequest, pbLeaseTimeToLiveResponse,
     GrpcSpec.md etcdLeaseTTLSpec, (@! etcdserverpb._Lease_LeaseTimeToLive_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.Lease/LeaseLeases", pbLeaseLeasesRequest, pbLeaseLeasesResponse,
     GrpcSpec.md etcdLeaseLeasesSpec, (@! etcdserverpb._Lease_LeaseLeases_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q⟩]

/-- **The lease reads as grpc runs them, at the KV's run slot with a thread token**
(`etcdGrpcSlot s E γr ∗ threadTok`, the one slot of a server serving both): the handler meets at
the contract's slot (`raftLeaseRead_server`'s `E.RD ∗ threadTok`, the store's reader `A.revR`)
rearranged (`grpcHandlerOk_slot`), promoted through the `*quotaLeaseServer` `q`, under the
interceptors. -/
theorem etcd_leaseReadMethodsOk (lp q s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γr : ReadNames) (γl : GName) (il im iu : GoFunc)
    (hA : A.revR = mvcc.storeReader E.s E.γ) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗
        v3rpc.raftLeaseRead s E γl iprop(E.RD ∗ threadTok) (mvcc.storeReader E.s E.γ) ∗
        auth.authPubLbM E.authMode 0 ∗ lease.lessorLb γl 0 ∗
        v3rpc.quotaLeaseServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ⊢
      [∗list] m ∈ etcdLeaseReadMethods q,
        grpcMethodOkMd m.handler m.srv [il, im, iu] iprop(etcdGrpcSlot s E γr ∗ threadTok) m.spec := by
  iintro ⟨#Pv, #Hat, #HL0, #Hn, #Hm, #Hq, #Hil, #Him, #Hiu⟩
  ihave #HL : v3rpc.raftLeaseRead s E γl iprop(E.RD ∗ threadTok) A.revR $$ []
  · rw [hA]; iexact HL0
  have h1 : iprop((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ threadTok) ⊢
      iprop(((E.RD ∗ threadTok) ∗ A.revR) ∗
        (srvLeadTimeReader s ∗ srvLgReader s ∗ srvReadReader s γr ∗ v3rpc.quotaRd s)) := by
    rw [hA]; unfold etcdRunSlot
    iintro ⟨⟨⟨Hlt, Hst, Hlg, Hrr, Hrd⟩, Hqr⟩, Ht⟩
    iframe
  have h2 : iprop(((E.RD ∗ threadTok) ∗ A.revR) ∗
        (srvLeadTimeReader s ∗ srvLgReader s ∗ srvReadReader s γr ∗ v3rpc.quotaRd s)) ⊢
      iprop((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ threadTok) := by
    rw [hA]; unfold etcdRunSlot
    iintro ⟨⟨⟨Hrd, Ht⟩, Hst⟩, Hlt, Hlg, Hrr, Hqr⟩
    iframe
  have h3 : iprop(etcdGrpcSlot s E γr ∗ threadTok) ⊢
      iprop((((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ threadTok) ∗
        [∗list] R ∈ etcdIcRs s, R) ∗ True) := by
    unfold etcdGrpcSlot
    iintro ⟨⟨Hrs, HRs⟩, Ht⟩
    iframe
  have h4 : iprop((((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ threadTok) ∗
        [∗list] R ∈ etcdIcRs s, R) ∗ True) ⊢ iprop(etcdGrpcSlot s E γr ∗ threadTok) := by
    unfold etcdGrpcSlot
    iintro ⟨⟨⟨Hrs, Ht⟩, HRs⟩, -⟩
    iframe
  ihave #Ht := etcd_leaseTTLHandlerOk lp s A cid mid E γl iprop(E.RD ∗ threadTok) 0 0 $$ []
  · iframe #
  ihave #Hl := etcd_leaseLeasesHandlerOk lp s A cid mid E γl iprop(E.RD ∗ threadTok) 0 0 $$ []
  · iframe #
  ihave #Ht' := grpcHandlerOk_slot _ _ _ _ etcdLeaseTTLSpec h1 h2 $$ Ht
  ihave #Hl' := grpcHandlerOk_slot _ _ _ _ etcdLeaseLeasesSpec h1 h2 $$ Hl
  ihave #Hqt := v3rpc.quotaLease_ttlHandlerOk etcdLeaseTTLSpec q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ threadTok) $$ [Hq Ht']
  · iframe #
  ihave #Hql := v3rpc.quotaLease_leasesHandlerOk etcdLeaseLeasesSpec q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ threadTok) $$ [Hq Hl']
  · iframe #
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmt := etcd_leaseTTLMethodOk q _ _ _ _ $$ [Hqt Ppb Hics]
  · iframe #
  ihave #Hml := etcd_leaseLeasesMethodOk q _ _ _ _ $$ [Hql Ppb Hics]
  · iframe #
  ihave #Hmt' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmt
  ihave #Hml' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hml
  ihave #Hmt'' := grpcMethodOkMd_slot _ _ _ _ _ _ _ h3 h4 $$ Hmt'
  ihave #Hml'' := grpcMethodOkMd_slot _ _ _ _ _ _ _ h3 h4 $$ Hml'
  simp only [etcdLeaseReadMethods]
  iframe #
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- **etcd's lease reads registered at `addr`** (persistent): what `examples/leasekv`'s client
calls. -/
def etcdLeaseReadAt (addr : GoString) : IProp GF :=
  iprop(isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseTimeToLive" etcdLeaseTTLSpec ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" etcdLeaseLeasesSpec)

instance etcdLeaseReadAt_persistent (addr : GoString) :
    Persistent (etcdLeaseReadAt (GF := GF) addr) := by
  unfold etcdLeaseReadAt; infer_instance

end served

end client
end EtcdGrove
end Perennial
