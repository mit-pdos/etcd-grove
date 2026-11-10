/-
**etcd's lease grant and listing, served at the lessor's history** (the lease-grant plan's 2.2,
2026-11-03, `notes/lease-grant-plan.md`). Lean-first (no Rocq counterpart).

The analogue of `LeaseReadServed.lean` for a cluster that grants leases: the `*LeaseServer`'s
`LeaseGrant` and `LeaseLeases`, promoted through the `*quotaLeaseServer`, meet the client's specs at
the lessor `γl`'s history (`etcdLeaseGrantSpec`, `etcdLeaseLeasesSpec`, `InvLeaseGrant.lean`):

* `etcd_leaseGrantHandlerOkL`: over the grant contract at the lessor's history
  (`v3rpc.lessorGrantOkL`), the reply's lease was granted at an index of the history;
* `etcd_leaseLeasesHandlerOkL`: over the lease-read contract, with auth off (Go's `LeaseLeases`
  errs, or lists nothing, only through `checkLeaseLeases`, `nil` with auth off: amendment (F3)), the
  listing is of an index no older than the caller's grants (`grants_lb`), so it has each of them
  (`grants_listed`: the lessor monotone);
* `etcd_leaseGrantMethodsOk`: `LeaseTimeToLive`, `LeaseLeases` and `LeaseGrant` as grpc runs them,
  at the KV's run slot with a thread token (as `etcd_leaseReadMethodsOk`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PerTypeLease
public import Proof.go_etcd_io.etcd.client.v3.LeaseReadServed
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseGrant

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section grants
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [lease_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **A lower bound of the history no older than each of the grants `G`** (from one bound `j`). -/
theorem grants_lb (γl : GName) (G : List w64) : ∀ j : Nat,
    lease.lessorLb (GF := GF) γl j ∗ ([∗list] id ∈ G, ∃ i : Nat, lease.leaseGrantedAt γl i id) ⊢
      ∃ m : Nat, ⌜j ≤ m⌝ ∗ lease.lessorLb γl m ∗
        [∗list] id ∈ G, ∃ i : Nat, ⌜i ≤ m⌝ ∗ lease.leaseGrantedAt γl i id := by
  induction G with
  | nil =>
    intro j
    iintro ⟨#Hj, -⟩
    iexists j
    iframe Hj
    isplitl []
    · ipureintro; exact Nat.le_refl j
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | cons id G ih =>
    intro j
    iintro ⟨#Hj, HG⟩
    icases BigSepL.bigSepL_cons.1 $$ HG with ⟨⟨%i, #Hi⟩, HG⟩
    ihave #Hij := lease.leaseGrantedAt_lb_max γl i j id $$ [Hi Hj]
    · iframe #
    ihave ⟨%m, %Hm, #Hm, HG'⟩ := ih (max i j) $$ [HG]
    · iframe Hij; iexact HG
    iexists m
    iframe Hm
    isplitl []
    · ipureintro; omega
    iapply BigSepL.bigSepL_cons.2
    iframe HG'
    iexists i
    iframe Hi
    ipureintro; omega

/-- **A listing at an index no older than the grants `G` has each of them** (the lessor monotone:
`leaseGrantedAt_listed`). -/
theorem grants_listed (γl : GName) (G : List w64) (m i : Nat) (ids : List w64) (hmi : m ≤ i) :
    lease.lessorRdInv (GF := GF) γl ∗
        ([∗list] id ∈ G, ∃ k : Nat, ⌜k ≤ m⌝ ∗ lease.leaseGrantedAt γl k id) ∗
        lease.leaseIdsAt γl i ids ⊢
      |={⊤}=> ⌜∀ id ∈ G, id ∈ ids⌝ := by
  induction G with
  | nil =>
    iintro -
    imodintro
    ipureintro
    intro id h
    cases h
  | cons id G ih =>
    iintro ⟨#Hinv, HG, #Hids⟩
    icases BigSepL.bigSepL_cons.1 $$ HG with ⟨⟨%k, %Hk, #Hk⟩, HG⟩
    imod (lease.leaseGrantedAt_listed γl k i id ids ⊤ (fun _ _ => CoPset.mem_full) (by omega))
      $$ [] with %h1
    · iframe #
    imod ih $$ [HG] with %h2
    · iframe #; iexact HG
    imodintro
    ipureintro
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact h2 x hx

end grants

section served
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **etcd's `LeaseGrant` handler meets etcd's `LeaseGrant` spec at a success fact `G`**
(`grpcHandlerOwnOk`; as `etcd_leaseGrantHandlerOk`, over the grant contract at `G`,
`v3rpc.lessorGrantOkG`; the lease-expiry plan's X2, 2026-11-04: until then at the history only,
`etcd_leaseGrantHandlerOkL`): the reply's lease has `G`; (E3, 2026-11-04) for the requests of the
contract's filter `R`, which the caller shows (`etcdLeaseGrantSpecGR`). -/
theorem etcd_leaseGrantHandlerOkGR (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γr : ReadNames) (on : Bool)
    (hNx : E.Nx = srvApi.kvNx γr on) (S : IProp GF) (G : w64 × w64 → w64 → IProp GF)
    [∀ m id, Persistent (G m id)] (R : w64 × w64 → Prop) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.lessorGrantOkG s E S G R ⊢
      grpcHandlerOwnOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseGrant") S
        (etcdLeaseGrantSpecGR (EM := v3rpc.etcdModelOfServer E γr on) G R) := by
  iintro ⟨#Pv, #Hat, #HL⟩
  unfold grpcHandlerOwnOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS, #Hctx, #Hrc, #Hr, Hid, HspecR⟩ HΨ
  iunfold etcdLeaseGrantSpecGR at HspecR
  icases HspecR with ⟨%HRm, Hspec⟩
  rw [show (pbLeaseGrantRequest (GF := GF)).recv r m = v3rpc.leaseGrantReqIs r m from rfl]
  rw [show (pbLeaseGrantRequest (GF := GF)).recvOwn r m = v3rpc.leaseGrantReqIdOwn r m.2 from rfl]
  iapply wp_fupd
  iapply (v3rpc.LeaseServer.wp_LeaseGrant lp s A cid mid E S G R ci cd r m)
    $$ [HS Hid]
  · iframe; iframe #; try (ipureintro; exact HRm)
  inext
  iintro %resp %err ⟨HS, Hout, Hg, #HSe⟩
  iunfold v3rpc.leaseGrantOut at Hout
  icases Hout with (⟨%Hok, Hh, #Hf⟩ | %Herr)
  · icases Hg with (%Hne | ⟨%id', #Hid', Hgr⟩)
    · exact absurd Hok.1 Hne
    iunfold v3rpc.leaseHdrOut at Hh
    icases Hh with ⟨%h, %rv, #Hhf, Hfd, -, #Hrev, #Hreach⟩
    iunfold v3rpc.hdrFilled at Hfd
    icases Hfd with ⟨%Hhn, %t, %ld, Hcid, Hmid, Ht, Hl⟩
    ipersist Hcid
    ipersist Hmid
    ipersist Ht
    ipersist Hl
    iunfold v3rpc.leaseGrantFields at Hf
    icases Hf with ⟨%id, %ttl, %e, #Hid, %Hid0, #Httl, #He⟩
    icombine Hid Hid' gives %Hii
    subst Hii
    imodintro
    iapply HΨ
    iframe HS HSe
    iintro -
    iexists (LeaseGrantRespM.mk (HdrM.mk cid mid rv t ld) id ttl e)
    isplitl []
    · simp only [pbLeaseGrantResponse]
      unfold leaseGrantRespMsg hdrFull
      isplitl []
      · ipureintro; exact Hok.2
      iexists h
      iframe #
      ipureintro; exact Hhn
    · iunfold etcdLeaseGrantSpecG at Hspec
      iapply Hspec
      · ipureintro; exact Hid0
      · iapply v3rpc.etcdReached_of_srvRevLb E γr on rv hNx $$ Hreach
      · iexact Hgr
  · imodintro
    iapply HΨ
    iframe HS HSe
    iintro %Hnil
    exact absurd Hnil Herr.2

/-- **etcd's `LeaseGrant` handler meets etcd's `LeaseGrant` spec at a success fact `G`**
(`etcd_leaseGrantHandlerOkGR` at the filter that covers every request). -/
theorem etcd_leaseGrantHandlerOkG (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γr : ReadNames) (on : Bool)
    (hNx : E.Nx = srvApi.kvNx γr on) (S : IProp GF) (G : w64 × w64 → w64 → IProp GF)
    [∀ m id, Persistent (G m id)] :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.lessorGrantOkG s E S G ⊢
      grpcHandlerOwnOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseGrant") S
        (etcdLeaseGrantSpecG (EM := v3rpc.etcdModelOfServer E γr on) G) := by
  iintro #H
  ihave #Hh := etcd_leaseGrantHandlerOkGR lp s A cid mid E γr on hNx S G (fun _ => True) $$ H
  unfold grpcHandlerOwnOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS, #Hctx, #Hrc, #Hr, Hid, Hspec⟩ HΨ
  iapply Hh $$ %m %Φ %ci %cd %r [HS Hid Hspec] HΨ
  iframe; iframe #
  unfold etcdLeaseGrantSpecGR
  iframe

/-- **etcd's `LeaseGrant` handler meets etcd's `LeaseGrant` spec at the lessor's history**
(`etcd_leaseGrantHandlerOkG` at the grant at the history, `v3rpc.lessorGrantOkL`): the reply's
lease was granted at an index of `(mvcc.api.mvccLeases E.γ)`'s history. -/
theorem etcd_leaseGrantHandlerOkL (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) (hNx : E.Nx = srvApi.kvNx γr on)
    (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.lessorGrantOkL s E S ⊢
      grpcHandlerOwnOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseGrant") S
        (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E γr on) (mvcc.api.mvccLeases E.γ)) := by
  exact etcd_leaseGrantHandlerOkG lp s A cid mid E γr on hNx S _

/-- **etcd's `LeaseLeases` handler meets etcd's `LeaseLeases` spec at the lessor `γl`'s history**
(as `etcd_leaseLeasesHandlerOk`), with auth off and the lessor's reader invariant: the call is made
at a lower bound no older than the caller's grants (`grants_lb`), and the listing, of an index no
older than it, has each of them (`grants_listed`); with auth off the server neither errs nor answers
the empty listing (amendment (F3)). -/
theorem etcd_leaseLeasesHandlerOkL (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γl : GName) (S : IProp GF) (n : Nat) (hoff : E.authOn = false) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLeaseRead s E γl S A.revR ∗
        auth.authPubLbM E.authMode n ∗ lease.lessorLb γl 0 ∗ lease.lessorRdInv γl ⊢
      grpcHandlerOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseLeases")
        iprop(S ∗ A.revR) (etcdLeaseLeasesSpec γl) := by
  iintro ⟨#Pv, #Hat, #HL, #Hn, #H0, #Hinv⟩
  unfold grpcHandlerOk
  iintro %req %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hrev⟩, #Hctx, #Hrc, -, Hspec⟩ HΨ
  iunfold etcdLeaseLeasesSpec at Hspec
  icases Hspec with ⟨%G, HG, Hk⟩
  ihave ⟨%m, -, #Hm, HG⟩ := grants_lb γl G 0 $$ [HG]
  · iframe H0; iexact HG
  iapply wp_fupd
  iapply (v3rpc.LeaseServer.wp_LeaseLeases lp s A cid mid E γl S ci cd r n m) $$ [HS Hrev]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hrev, Hout, #HSe⟩
  iunfold v3rpc.leaseLeasesOut at Hout
  icases Hout with (⟨%Hok, %w, Hw, Hres⟩ | %Herr)
  · ihave %Hnn := typedPointsto_not_null $$ Hw
    iStructNamedSuffix Hw "_f"
    ipersist Header_f
    ipersist Leases_f
    icases Hres with (⟨%i, %ids, %Hmi, #Hids, Hh, Hl, -⟩ | ⟨%Hon, -, -⟩)
    rotate_left
    · rw [hoff] at Hon; cases Hon
    ihave %Hnd := lease.leaseIdsAt_nodup γl i ids $$ Hids
    imod grants_listed γl G m i ids Hmi $$ [HG] with %HGl
    · iframe #; iexact HG
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
    · iapply Hk
      ipureintro; exact ⟨Hnd, HGl⟩
  · imodintro
    iapply HΨ
    iframe HS Hrev HSe
    iintro %Hnil
    exact absurd Hnil Herr.2.1

/-- **etcd's lease reads and grant at the lessor's history** as registered: `LeaseTimeToLive`,
`LeaseLeases` and `LeaseGrant`, the generated handlers of `Lease_ServiceDesc` with the
`*quotaLeaseServer` `q`, with etcd's specs at `(mvcc.api.mvccLeases E.γ)` (the listing's and the grant's). -/
def etcdLeaseGrantMethods (q : Loc) (E : apply.AEnv GF) (γr : ReadNames) : List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.Lease/LeaseTimeToLive", pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT,
     GrpcSpec.md etcdLeaseTTLSpec, (@! etcdserverpb._Lease_LeaseTimeToLive_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseTimeToLiveRequestT_reg, pbLeaseTimeToLiveResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Lease/LeaseLeases", pbLeaseLeasesRequestT, pbLeaseLeasesResponseT,
     GrpcSpec.md (etcdLeaseLeasesSpec (mvcc.api.mvccLeases E.γ)), (@! etcdserverpb._Lease_LeaseLeases_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseLeasesRequestT_reg, pbLeaseLeasesResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Lease/LeaseGrant", pbLeaseGrantRequestT, pbLeaseGrantResponseT,
     GrpcSpec.md (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)),
     (@! etcdserverpb._Lease_LeaseGrant_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseGrantRequestT_reg, pbLeaseGrantResponseT_reg⟩]

/-- **The lease reads and the grant as grpc runs them, at the KV's run slot with a thread token**
(as `etcd_leaseReadMethodsOk`): the reads at the lease-read contract's slot, the grant at the
grant contract's `etcdRunSlot s E γr ∗ threadTok` (its quota check's readers added by the
`*quotaLeaseServer`), each rearranged into `etcdGrpcSlot s E γr ∗ threadTok`. -/
theorem etcd_leaseGrantMethodsOk (lp q s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γr : ReadNames) (il im iu : GoFunc)
    (hA : A.revR = mvcc.api.mvccReaders E.γ 1) (hoff : E.authOn = false)
    (hNx : E.Nx = srvApi.kvNx γr false) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.leaseServerAt lp s A cid mid ∗
        v3rpc.raftLeaseRead s E (mvcc.api.mvccLeases E.γ) iprop(E.RD ∗ threadTok) (mvcc.api.mvccReaders E.γ 1) ∗
        v3rpc.lessorGrantOkL s E iprop(etcdRunSlot s E γr ∗ threadTok) ∗
        auth.authPubLbM E.authMode 0 ∗ lease.lessorLb (mvcc.api.mvccLeases E.γ) 0 ∗
        lease.lessorRdInv (mvcc.api.mvccLeases E.γ) ∗
        v3rpc.quotaLeaseServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ⊢
      [∗list] m ∈ etcdLeaseGrantMethods q E γr,
        grpcMethodOkMd m.handler m.srv [il, im, iu] iprop(etcdGrpcSlot s E γr ∗ threadTok) m.spec := by
  iintro ⟨#Pv, #Ps, #Hat, #HL0, #HG, #Hn, #Hm, #Hinv, #Hq, #Hil, #Him, #Hiu⟩
  ihave #HL : v3rpc.raftLeaseRead s E (mvcc.api.mvccLeases E.γ) iprop(E.RD ∗ threadTok) A.revR $$ []
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
  have h5 : iprop(etcdGrpcSlot s E γr ∗ threadTok) ⊢
      iprop((((etcdRunSlot s E γr ∗ threadTok) ∗ v3rpc.quotaRd s) ∗
        [∗list] R ∈ etcdIcRs s, R) ∗ True) := by
    unfold etcdGrpcSlot
    iintro ⟨⟨⟨Hrs, Hqr⟩, HRs⟩, Ht⟩
    iframe
  have h6 : iprop((((etcdRunSlot s E γr ∗ threadTok) ∗ v3rpc.quotaRd s) ∗
        [∗list] R ∈ etcdIcRs s, R) ∗ True) ⊢ iprop(etcdGrpcSlot s E γr ∗ threadTok) := by
    unfold etcdGrpcSlot
    iintro ⟨⟨⟨⟨Hrs, Ht⟩, Hqr⟩, HRs⟩, -⟩
    iframe
  ihave #Ht := etcd_leaseTTLHandlerOk lp s A cid mid E (mvcc.api.mvccLeases E.γ) iprop(E.RD ∗ threadTok) 0 0 $$ []
  · iframe #
  ihave #Hl := etcd_leaseLeasesHandlerOkL lp s A cid mid E (mvcc.api.mvccLeases E.γ) iprop(E.RD ∗ threadTok) 0
    hoff $$ []
  · iframe #
  ihave #Hg := etcd_leaseGrantHandlerOkL lp s A cid mid E γr false hNx iprop(etcdRunSlot s E γr ∗ threadTok)
    $$ []
  · iframe #
  ihave #Ht' := grpcHandlerOk_slot _ _ _ _ etcdLeaseTTLSpec h1 h2 $$ Ht
  ihave #Hl' := grpcHandlerOk_slot _ _ _ _ (etcdLeaseLeasesSpec (mvcc.api.mvccLeases E.γ)) h1 h2 $$ Hl
  ihave #Hqt := v3rpc.quotaLease_ttlHandlerOk etcdLeaseTTLSpec q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ threadTok) $$ [Hq Ht']
  · iframe #
  ihave #Hql := v3rpc.quotaLease_leasesHandlerOk (etcdLeaseLeasesSpec (mvcc.api.mvccLeases E.γ)) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ threadTok) $$ [Hq Hl']
  · iframe #
  ihave #Hqg := v3rpc.quotaLease_grantHandlerOk_of v3rpc.quotaLeaseServer.wp_LeaseGrant
    (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop(etcdRunSlot s E γr ∗ threadTok) $$ []
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
  ihave #Hmg := etcd_leaseGrantMethodOk q _ _ _ _ $$ [Hqg Ppb Hics]
  · iframe #
  ihave #Hmt' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmt
  ihave #Hml' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hml
  ihave #Hmg' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmg
  ihave #Hmt'' := grpcMethodOkMd_slot _ _ _ _ _ _ _ h3 h4 $$ Hmt'
  ihave #Hml'' := grpcMethodOkMd_slot _ _ _ _ _ _ _ h3 h4 $$ Hml'
  ihave #Hmg'' := grpcMethodOkMd_slot _ _ _ _ _ _ _ h5 h6 $$ Hmg'
  simp only [etcdLeaseGrantMethods, pbLeaseGrantRequestT, pbLeaseGrantResponseT, pbLeaseLeasesRequestT, pbLeaseLeasesResponseT, pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT]
  iframe #
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- **etcd's `LeaseTimeToLive` handler meets the revocable mode's spec** (`etcdLeaseTTLSpecLive`;
the lease-expiry plan's E3, 2026-11-05), over the lease-read contract at the run resource `S` and the
revision reader `A.revR`, at the auth store's lower bound `n`: the call is made at the caller's lower
bound `m` of the lessor's history, and `LeaseServer.LeaseTimeToLive`'s answer (`leaseTTLOut`) carries
the server's facts under the lease-TTL row: its own TTL `-1` reply the not-found one. -/
theorem etcd_leaseTTLHandlerOkLive (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γl : GName) (S : IProp GF) (n : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLeaseRead s E γl S A.revR ∗
        auth.authPubLbM E.authMode n ⊢
      grpcHandlerOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseTimeToLive")
        iprop(S ∗ A.revR) (etcdLeaseTTLSpecLive γl s) := by
  iintro ⟨#Pv, #Hat, #HL, #Hn⟩
  unfold grpcHandlerOk
  iintro %req %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hrev⟩, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  iunfold etcdLeaseTTLSpecLive at Hspec
  icases Hspec with ⟨%m, #Hm, Hk⟩
  rw [show (pbLeaseTimeToLiveRequest (GF := GF)).recv r req =
      iprop(∃ v : etcdserverpb.LeaseTimeToLiveRequest, r ↦□ v ∗ ⌜(v.ID', v.Keys') = req⌝) from rfl]
  icases Hr with ⟨%v, #Hv, %Hvm⟩
  iapply wp_fupd
  iapply (v3rpc.LeaseServer.wp_LeaseTimeToLive lp s A cid mid E γl S ci cd r DFrac.discard v n m)
    $$ [HS Hrev]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hrev, -, Hout, #HSe⟩
  iunfold v3rpc.leaseTTLOut at Hout
  icases Hout with (⟨%Hok, %w, Hw, %Hid, Hh, Harm⟩ | %Herr)
  · ihave #Hf : □ (leaseTTLRow s γl -∗
        (∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i v.ID' w.GrantedTTL') ∨
        lease.leaseAbsentFrom γl m v.ID') $$ [Harm]
    · icases Harm with (⟨-, -, #Hf⟩ | ⟨-, #Hnf⟩)
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
    · have hid' : (LeaseTTLRespM.mk (HdrM.mk cid mid rv t ld) w.ID' w.TTL' w.GrantedTTL').id =
          req.1 := by
        simp only; rw [Hid, ← Hvm]
      iapply Hk $$ %(LeaseTTLRespM.mk (HdrM.mk cid mid rv t ld) w.ID' w.TTL' w.GrantedTTL') %hid'
      simp only
      rw [Hid]
      iexact Hf
  · imodintro
    iapply HΨ
    iframe HS Hrev HSe
    iintro %Hnil
    exact absurd Hnil Herr.2

/-- **etcd's `LeaseLeases` handler meets the revocable mode's spec** (`etcdLeaseLeasesSpecLive`; the
lease-expiry plan's E3, 2026-11-05), with auth off: the call is made at the caller's lower bound `m`
of the lessor's history, and the listing is the lessor's ids at an index `≥ m` (`leaseLeasesOut`'s;
with auth off the server answers neither an error nor the empty listing, amendment (F3)). -/
theorem etcd_leaseLeasesHandlerOkLive (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γl : GName) (S : IProp GF) (n : Nat) (hoff : E.authOn = false) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLeaseRead s E γl S A.revR ∗
        auth.authPubLbM E.authMode n ⊢
      grpcHandlerOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseLeases")
        iprop(S ∗ A.revR) (etcdLeaseLeasesSpecLive γl) := by
  iintro ⟨#Pv, #Hat, #HL, #Hn⟩
  unfold grpcHandlerOk
  iintro %req %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hrev⟩, #Hctx, #Hrc, -, Hspec⟩ HΨ
  iunfold etcdLeaseLeasesSpecLive at Hspec
  icases Hspec with ⟨%m, #Hm, Hk⟩
  iapply wp_fupd
  iapply (v3rpc.LeaseServer.wp_LeaseLeases lp s A cid mid E γl S ci cd r n m) $$ [HS Hrev]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hrev, Hout, #HSe⟩
  iunfold v3rpc.leaseLeasesOut at Hout
  icases Hout with (⟨%Hok, %w, Hw, Hres⟩ | %Herr)
  · ihave %Hnn := typedPointsto_not_null $$ Hw
    iStructNamedSuffix Hw "_f"
    ipersist Header_f
    ipersist Leases_f
    icases Hres with (⟨%i, %ids, %Hmi, #Hids, Hh, Hl, -⟩ | ⟨%Hon, -, -⟩)
    rotate_left
    · rw [hoff] at Hon; cases Hon
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
    · iapply Hk
      iexists i
      iframe Hids
      ipureintro; exact Hmi
  · imodintro
    iapply HΨ
    iframe HS Hrev HSe
    iintro %Hnil
    exact absurd Hnil Herr.2.1

/-- **etcd's lease reads and grant in the revocable lease mode** as registered (the lease-expiry
plan's X2, 2026-11-04; the reads at the revocable mode's specs since E3, 2026-11-05):
`LeaseTimeToLive` at the lessor `(mvcc.api.mvccLeases E.γ)` and the server `s` (`etcdLeaseTTLSpecLive`), `LeaseLeases`
at the lessor's history from the caller's lower bound (`etcdLeaseLeasesSpecLive`: no grant listed, since
a revocable lessor need not list a lease it granted) and `LeaseGrant` at the live spec
(`etcdLeaseGrantSpecLive`), the generated handlers of `Lease_ServiceDesc` with the
`*quotaLeaseServer` `q`. -/
def etcdLeaseGrantLiveMethods (q s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.Lease/LeaseTimeToLive", pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT,
     GrpcSpec.md (etcdLeaseTTLSpecLive (mvcc.api.mvccLeases E.γ) s),
     (@! etcdserverpb._Lease_LeaseTimeToLive_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseTimeToLiveRequestT_reg, pbLeaseTimeToLiveResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Lease/LeaseLeases", pbLeaseLeasesRequestT, pbLeaseLeasesResponseT,
     GrpcSpec.md (etcdLeaseLeasesSpecLive (mvcc.api.mvccLeases E.γ)),
     (@! etcdserverpb._Lease_LeaseLeases_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseLeasesRequestT_reg, pbLeaseLeasesResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Lease/LeaseGrant", pbLeaseGrantRequestT, pbLeaseGrantResponseT,
     GrpcSpec.md (etcdLeaseGrantSpecLive (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)),
     (@! etcdserverpb._Lease_LeaseGrant_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q, pbLeaseGrantRequestT_reg, pbLeaseGrantResponseT_reg⟩]

/-- **The lease reads and the live grant as grpc runs them, at the KV's run slot with a thread
token** (as `etcd_leaseGrantMethodsOk`): the reads at the revocable mode's specs
(`etcd_leaseTTLHandlerOkLive`, `etcd_leaseLeasesHandlerOkLive`, auth off), the grant over the grant
contract at the mode-free fact (`v3rpc.grantLiveG`). -/
theorem etcd_leaseGrantLiveMethodsOk (lp q s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γr : ReadNames) (il im iu : GoFunc)
    (hA : A.revR = mvcc.api.mvccReaders E.γ 1) (hoff : E.authOn = false)
    (hNx : E.Nx = srvApi.kvNx γr false) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.leaseServerAt lp s A cid mid ∗
        v3rpc.raftLeaseRead s E (mvcc.api.mvccLeases E.γ) iprop(E.RD ∗ threadTok) (mvcc.api.mvccReaders E.γ 1) ∗
        v3rpc.lessorGrantOkG s E iprop(etcdRunSlot s E γr ∗ threadTok) (v3rpc.grantLiveG E)
          (fun m => m.2 = W64 0) ∗
        auth.authPubLbM E.authMode 0 ∗ lease.lessorLb (mvcc.api.mvccLeases E.γ) 0 ∗
        v3rpc.quotaLeaseServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ⊢
      [∗list] m ∈ etcdLeaseGrantLiveMethods q s E γr,
        grpcMethodOkMd m.handler m.srv [il, im, iu] iprop(etcdGrpcSlot s E γr ∗ threadTok) m.spec := by
  iintro ⟨#Pv, #Ps, #Hat, #HL0, #HG, #Hn, #Hm, #Hq, #Hil, #Him, #Hiu⟩
  ihave #HL : v3rpc.raftLeaseRead s E (mvcc.api.mvccLeases E.γ) iprop(E.RD ∗ threadTok) A.revR $$ []
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
  ihave #Ht := etcd_leaseTTLHandlerOkLive lp s A cid mid E (mvcc.api.mvccLeases E.γ) iprop(E.RD ∗ threadTok) 0
    $$ []
  · iframe #
  ihave #Hl := etcd_leaseLeasesHandlerOkLive lp s A cid mid E (mvcc.api.mvccLeases E.γ) iprop(E.RD ∗ threadTok) 0
    hoff $$ []
  · iframe #
  ihave #Ht' := grpcHandlerOk_slot _ _ _ _ (etcdLeaseTTLSpecLive (mvcc.api.mvccLeases E.γ) s) h1 h2 $$ Ht
  ihave #Hl' := grpcHandlerOk_slot _ _ _ _ (etcdLeaseLeasesSpecLive (mvcc.api.mvccLeases E.γ)) h1 h2 $$ Hl
  ihave #Hqt := v3rpc.quotaLease_ttlHandlerOk (etcdLeaseTTLSpecLive (mvcc.api.mvccLeases E.γ) s) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ threadTok) $$ [Hq Ht']
  · iframe #
  ihave #Hql := v3rpc.quotaLease_leasesHandlerOk (etcdLeaseLeasesSpecLive (mvcc.api.mvccLeases E.γ)) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ threadTok) $$ [Hq Hl']
  · iframe #
  ihave #Hics0 : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb0 : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmt0 := etcd_leaseTTLMethodOk q _ _ _ _ $$ [Hqt Ppb0 Hics0]
  · iframe #
  ihave #Hml0 := etcd_leaseLeasesMethodOk q _ _ _ _ $$ [Hql Ppb0 Hics0]
  · iframe #
  ihave #Hmt1 := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmt0
  ihave #Hml1 := (grpcMethodOk_md _ _ _ _ _).1 $$ Hml0
  ihave #Hmt := grpcMethodOkMd_slot _ _ _ _ _ _ _ h3 h4 $$ Hmt1
  ihave #Hml := grpcMethodOkMd_slot _ _ _ _ _ _ _ h3 h4 $$ Hml1
  have h5 : iprop(etcdGrpcSlot s E γr ∗ threadTok) ⊢
      iprop((((etcdRunSlot s E γr ∗ threadTok) ∗ v3rpc.quotaRd s) ∗
        [∗list] R ∈ etcdIcRs s, R) ∗ True) := by
    unfold etcdGrpcSlot
    iintro ⟨⟨⟨Hrs, Hqr⟩, HRs⟩, Ht⟩
    iframe
  have h6 : iprop((((etcdRunSlot s E γr ∗ threadTok) ∗ v3rpc.quotaRd s) ∗
        [∗list] R ∈ etcdIcRs s, R) ∗ True) ⊢ iprop(etcdGrpcSlot s E γr ∗ threadTok) := by
    unfold etcdGrpcSlot
    iintro ⟨⟨⟨⟨Hrs, Ht⟩, Hqr⟩, HRs⟩, -⟩
    iframe
  have hg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗
        v3rpc.lessorGrantOkG s E iprop(etcdRunSlot s E γr ∗ threadTok) (v3rpc.grantLiveG E)
          (fun m => m.2 = W64 0) ⊢
      grpcHandlerOwnOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseGrant")
        iprop(etcdRunSlot s E γr ∗ threadTok)
        (etcdLeaseGrantSpecLive (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)) :=
    etcd_leaseGrantHandlerOkGR lp s A cid mid E γr false hNx iprop(etcdRunSlot s E γr ∗ threadTok)
      (v3rpc.grantLiveG E) (fun m => m.2 = W64 0)
  ihave #Hg := hg $$ []
  · iframe #
  ihave #Hqg := v3rpc.quotaLease_grantHandlerOk_of v3rpc.quotaLeaseServer.wp_LeaseGrant
    (etcdLeaseGrantSpecLive (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop(etcdRunSlot s E γr ∗ threadTok) $$ []
  · iframe #
  ihave #Hmg := etcd_leaseGrantMethodOk q _ _ _ _ $$ [Hqg Ppb0 Hics0]
  · iframe #
  ihave #Hmg' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmg
  ihave #Hmg'' := grpcMethodOkMd_slot _ _ _ _ _ _ _ h5 h6 $$ Hmg'
  simp only [etcdLeaseGrantLiveMethods, pbLeaseGrantRequestT, pbLeaseGrantResponseT, pbLeaseLeasesRequestT, pbLeaseLeasesResponseT, pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT]
  iframe #
  iapply BigSepL.bigSepL_nil.2
  itrivial

end served

end client
end EtcdGrove
end Perennial
