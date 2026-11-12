/-
**etcd's KV calls and lease reads registered at a served member's address** (the closed lease
example, 2026-11-02, `notes/lease-ex-plan.md`). Lean-first (no Rocq counterpart).

`kv_lease_served`: `kv_served`'s ghost step, with the Lease service's reads served too
(`client.etcdLeaseReadAt`: `LeaseTimeToLive`, `LeaseLeases` at etcd's specs), from `grpcUp`'s
Lease service (`grpcLeaseUp`) and the member's lessor reader side (`memberUp`'s `srvLeaseRd`). One
`grpc.serve` serves every method, with one slot: the KV's run resources and the level-0 token
(`etcdGrpcSlot s E γr ∗ levelTok 0`, a run's bundle `srvRunBundle` by `client.etcdGrpcSlot_bundle`),
which each run borrows from the server's run pools, built here from `memberUp`'s stocks
(`kvServeStocks_pools`; per-type stage B3: until then a thread token the caller gave). The lease
reads take the token with `E.RD` and the store's reader (`raftLeaseRead_server`'s
`E.RD ∗ levelTok 0`); the KV's runs frame it through.

In a cluster that grants leases (the KV names' `lg`; the lease-grant plan's 2.2, 2026-11-03: one lemma
taking `lg`, which replaced the draft `kv_lease_grant_served`), `LeaseGrant` and `LeaseLeases` are
registered at the specs at the lessor's history instead (`etcdLeaseGrantAt`): a grant's reply carries
its lease's grant (`etcdLeaseGrantSpec`), and a listing lists every grant the caller hands in
(`etcdLeaseLeasesSpec`); the KV's registrations are not passed on (the KV service makes no claim in
that cluster, the plan's Q1). The grant handler calls the server's (`v3rpc.lessorGrantOkL_server`).
`kv_lease_served_false`: the post at `lg = false`, as before. `kv_lease_served_watch` (lease-mono3's
pass 2(c), 2026-11-06): the same, with the member's `Watch` stream served at the address,
`noRefusalAt` and `srvGoRes` (what `cluster3.memberServed` keeps in every lease mode).

Why one member's lessor (review S5): the contracts name `(mvcc.api.mvccLeases E.γ)`, this member's, not a
cluster-level certificate, because Go's listing is member-local: `LeaseLeases` reads the member's
own lessor without a read index (`v3_server.go:737-749`), so a lagging member need not list a lease
the cluster granted, and a cluster-level contract would be false. With several endpoints the client
would need the contracts at every member, which no granting cluster gives.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.go_etcd_io.etcd.client.v3.LeaseReadServed
public import Proof.go_etcd_io.etcd.client.v3.LeaseGrantServed
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseSrc

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`LeaseGrant` and `LeaseLeases` registered at the specs at the lessor `(mvcc.api.mvccLeases E.γ)`'s
history** (persistent). Per member, not per cluster: `LeaseLeases` is a member-local read (see
the file header). -/
def etcdLeaseGrantAt (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant"
      (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)) ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpec (mvcc.api.mvccLeases E.γ)))

instance etcdLeaseGrantAt_persistent (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (etcdLeaseGrantAt addr E γr) := by
  unfold etcdLeaseGrantAt; infer_instance

omit [HasExt idIssueExt] cache_sem in
/-- **`etcdLeaseGrantAt` gives its two registrations** (lease-mono3's review r2, N1: the
elimination a client uses in place of unfolding the definition). -/
theorem etcdLeaseGrantAt_elim (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames) :
    etcdLeaseGrantAt addr E γr ⊢
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant"
          (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)) ∗
        isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpec (mvcc.api.mvccLeases E.γ)) := by
  iintro #H
  iunfold etcdLeaseGrantAt at H
  iexact H

/-- **`LeaseGrant`, `LeaseTimeToLive` and `LeaseLeases` registered at the revocable mode's specs**
(persistent; the lease-expiry plan's X2, 2026-11-04, the reads since E3, 2026-11-05): a grant's reply
carries its lease live in the lessor `(mvcc.api.mvccLeases E.γ)`'s history and its request, the requested TTL
(`etcdLeaseGrantSpecLive`; the lease-expiry plan's S2–S4, Q-S8; review r1 F12: until then the
lease's read-only `ttl` field at least the request); a TTL reply, at the caller's lower bound of the history, the lease's TTL there or its absence, under the
lease-TTL row of the server `s` (`etcdLeaseTTLSpecLive`); a listing, the lease ids of a snapshot no
older than the caller's lower bound (`etcdLeaseLeasesSpecLive`: no grant listed, the lessor may have
revoked it). -/
def etcdLeaseGrantLiveAt (addr : GoString) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant"
      (etcdLeaseGrantSpecLive (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)) ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseTimeToLive" (etcdLeaseTTLSpecLive (mvcc.api.mvccLeases E.γ) s) ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpecLive (mvcc.api.mvccLeases E.γ)))

instance etcdLeaseGrantLiveAt_persistent (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) : Persistent (etcdLeaseGrantLiveAt addr s E γr) := by
  unfold etcdLeaseGrantLiveAt; infer_instance

/-- **What a served member registers besides the lease reads, by its lease mode `m`** (the
lease-expiry plan's X2, 2026-11-04): the KV calls in the mode `none` (a cluster that grants no
lease); the grant and the listing at the lessor's history in the monotone mode (`etcdLeaseGrantAt`);
the grant at the live spec and the reads at the server `s`'s lessor in the revocable mode
(`etcdLeaseGrantLiveAt`). -/
def etcdLeaseServedAt (m : lease.Mode) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) : IProp GF :=
  match m with
  | .none => etcdKVAt addr E ρ γr cid mid
  | .mono => etcdLeaseGrantAt addr E γr
  | .revocable => etcdLeaseGrantLiveAt addr s E γr

instance etcdLeaseServedAt_persistent (m : lease.Mode) (addr : GoString) (s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) :
    Persistent (etcdLeaseServedAt m addr s E ρ γr cid mid) := by
  cases m <;> unfold etcdLeaseServedAt <;> infer_instance

omit [HasExt idIssueExt] cache_sem in
/-- **`etcdLeaseServedAt` in the mode `none` is the KV calls** (`rfl`; lease-mono3's review r2,
N1). -/
theorem etcdLeaseServedAt_none (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid : w64) :
    etcdLeaseServedAt .none addr s E ρ γr cid mid = etcdKVAt addr E ρ γr cid mid := rfl

omit [HasExt idIssueExt] cache_sem in
/-- **`etcdLeaseServedAt` in the monotone mode is the grant and the listing at the lessor's
history** (`rfl`; lease-mono3's review r2, N1). -/
theorem etcdLeaseServedAt_mono (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid : w64) :
    etcdLeaseServedAt .mono addr s E ρ γr cid mid = etcdLeaseGrantAt addr E γr := rfl

/-- **`kv_lease_served`, with what the watch service needs** (lease-mono3's pass 2(c),
2026-11-06): its post, and the `GoAttach` resources `grpcUp` holds (`srvGoRes`), the stream
registrations `grpc.start` gives (`grpcStreamServerAt` of the server `γ`, from
`etcd_kv_started_with`), the watch server with its stream chain's contracts, and the server's run
pools (`srvRevokeBuilt`, `srvRunPool`, persistent: what the watch runs borrow from; per-type stage
B3, until then one watch run slot). Private: `kv_lease_served` and `kv_lease_served_watch` are its
two views. -/
private theorem kv_lease_served_core (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hP : leasePeersOk) (hρ : ρ.rd = γr) (m : lease.Mode)
    (hm : ρ.rd.kv.lm = m) (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E m ∗
        kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> ∃ γ : GName, grpcServeTok gs lis γ ∗ srvGoRes s ∗
        (∃ (pw : Loc) (ims is : GoFunc) (sregs : List (GoString × GoFunc × GoInterface)),
          ⌜v3rpc.watchSReg pw ∈ sregs ∧ R.s = s ∧ R.E = E⌝ ∗
          grpcStreamServerAt addr [ims, is] sregs γ ∗ v3rpc.isWatchServer pw R ∗
          srvStreamInterceptorOk ims iprop(True) ∗ srvStreamInterceptorOk is iprop(True) ∗
          srvRevokeBuilt s E ∗ srvRunPool s E γr) ∗
        client.etcdLeaseReadAt addr ∗ etcdLeaseServedAt m addr s E ρ γr cid mid := by
  iintro ⟨#Pv3, #Psrv, #Hreq, #Hrd, #Hlr, Hstk, Hup⟩
  iunfold grpcUp at Hup
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, Hgo, Hlis, #Hlu⟩
  obtain ⟨HCA, -, Hregs, Hwreg, hRs, hRE, -, -, Hnd⟩ := HC
  -- the run pools, built from `memberUp`'s stocks
  imod (kvServeStocks_pools s E γr ⊤) $$ Hstk with ⟨#Hrp, #Hb⟩
  -- the one gRPC slot, a run's bundle with its level-0 token
  have h1 : srvRunBundle s E γr ⊢
      iprop(client.etcdGrpcSlot s E γr ∗ levelTok 0) ∗ iprop(True) := by
    iintro H
    ihave H := (client.etcdGrpcSlot_bundle s E γr).1 $$ H
    iframe
  have h2 : iprop(client.etcdGrpcSlot s E γr ∗ levelTok 0) ∗ iprop(True) ⊢
      srvRunBundle s E γr := by
    iintro ⟨H, -⟩
    iapply (client.etcdGrpcSlot_bundle s E γr).2
    iexact H
  -- the lease reads' contract (`raftLeaseRead_server`), auth off
  ihave %Hoff := isServerReq_authOff s E ρ $$ Hreq
  have hM : E.authMode = .off := by
    unfold apply.AEnv.authOn at Hoff
    cases hM : E.authMode <;> simp_all [auth.AuthMode.isOn]
  ihave #Hauth := srvAuthAt_of_views s E ρ γr $$ []
  · iframe #
  ihave #HaLb := srvAuthLb_off s E ρ $$ Hreq
  ihave #HrdM : isServerReadM E.authOn s E γr $$ []
  · rw [Hoff, isServerReadM_false]; iexact Hrd
  ihave #HreqM : isServerReqM E.authOn s E ρ $$ []
  · rw [Hoff, isServerReqM_false]; iexact Hreq
  -- (R9, the `lean` merge) the read view's witness, the model's tie (`E.Nx = kvNx γr false`)
  ihave %hNx : ⌜E.Nx = srvApi.kvNx γr false⌝ $$ []
  · ihave #Hinvs := srvKVInvs_of_read s E γr $$ Hrd
    iunfold srvKVInvs at Hinvs
    icases Hinvs with ⟨-, -, -, -, -, %h, -⟩
    ipureintro; rw [h]; rfl
  ihave #HaLL := srvAuthLeaseLb_of_server s E γr (Or.inl hM) $$ []
  · iframe #
  icases v3rpc.srvHeaderFacts_server E.authOn s E ρ $$ HreqM with ⟨%cs, %ms, #Hhf⟩
  iunfold srvLeaseRd at Hlr
  icases Hlr with ⟨%on, #Hli⟩
  ihave ⟨#Hlrd, #Hpool⟩ := lease.srvInv_lessorRd on s E m $$ Hli
  ihave #HLR := v3rpc.raftLeaseRead_server s E ρ γr (mvcc.api.mvccLeases E.γ) cs ms HT
      (Nat.le_trans Hrb (Nat.pow_le_pow_right (by decide) (by decide))) hP $$ []
  · iframe #
  -- the lower bounds `0`
  ihave #HRI : lease.lessorRdInv (mvcc.api.mvccLeases E.γ) $$ []
  · iunfold srvLessorRd at Hlrd
    icases Hlrd with ⟨%lp, -, #Hinv⟩
    iunfold lease.lessorInv at Hinv
    icases Hinv with ⟨-, -, -, #H⟩
    iexact H
  imod (lease.lessorLb_get (mvcc.api.mvccLeases E.γ) ⊤ (fun _ _ => CoPset.mem_full)) $$ HRI with ⟨%m0, #Hlb⟩
  ihave #Hlb0 := lease.lessorLb_le (mvcc.api.mvccLeases E.γ) 0 (Nat.zero_le _) $$ Hlb
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hpub
  -- the lease reads' meets, at the slot
  iunfold grpcLeaseUp at Hlu
  icases Hlu with ⟨%ql, %pl, %lcid, %lmid, %HLr, #Hql, #Hlat⟩
  ihave #Hkva := client.kvServerAt_of_is p s C.A cid mid C.n $$ Hkvs
  ihave #Hil' := Hil $$ %v3rpc.learnerReqOk
  ihave #Him' := Him $$ %v3rpc.learnerReqOk
  cases m with
  | none =>
    -- the KV calls and the lease reads
    ihave #Hlms := client.etcd_leaseReadMethodsOk pl ql s C.A lcid lmid E γr (mvcc.api.mvccLeases E.γ) il im iu
        (by rw [HCA]; rfl) $$ []
    · iframe #
    ihave #Hks := client.srvRunOks_of_slot s E γr [il, im, iu]
        iprop(client.etcdGrpcSlot s E γr ∗ levelTok 0) iprop(True) h1 h2 HL
        (client.etcdLeaseReadMethods ql) $$ []
    · iframe #
    rw [HCA]
    imod (client.etcd_kv_started_with addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
        sregs (client.etcdLeaseReadMethods ql)
        Hregs
        (by
          intro m hm
          apply HLr
          simp only [client.etcdLeaseReadMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl <;> simp [v3rpc.leaseRegs])
        Hrf Hnd hρ HL) $$ [Hgsn Hlis] with ⟨%γ, Hserv, Hss, #HPut, #HRange, #HDel, #HTxn, #HCmp, Hle⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb
    simp only [client.etcdLeaseReadMethods, pbLeaseLeasesRequestT, pbLeaseLeasesResponseT, pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT]
    icases Hle with ⟨#H1, #H2, -⟩
    ihave #H1' := (isGrpcRpc_md _ _ _).2 $$ H1
    ihave #H2' := (isGrpcRpc_md _ _ _).2 $$ H2
    imodintro
    iexists γ
    iframe Hserv Hgo
    isplitl [Hss]
    · iexists pw, ims, is, sregs
      iframe; iframe #
      ipureintro; exact ⟨Hwreg, hRs, hRE⟩
    simp only [etcdLeaseServedAt]
    iunfold etcdKVAt
    iunfold client.etcdLeaseReadAt
    iframe #
  | mono =>
    -- the monotone mode: the lease reads and the grant at the lessor's history
    have hlg : ρ.rd.kv.lg = true := by rw [KVNames.lg_eq, hm]; decide
    ihave #HGL := v3rpc.lessorGrantOkL_server s E ρ iprop(client.etcdRunSlot s E γr ∗ levelTok 0)
        ⟨hlg, Hoff⟩ (by rw [hm]; decide) on $$ []
    · iframe #
      isplitr
      · iintro !>
        imodintro
        iunfold idCred
        ipureintro; exact Hrb
      iintro !> ⟨HR, Ht⟩
      unfold client.etcdRunSlot
      icases HR with ⟨Hlt, Hst, Hlg, Hrr, Hrd⟩
      iframe Hlt Hrd
      iintro ⟨Hlt, Hrd⟩
      iframe
    ihave #Hlms := client.etcd_leaseGrantMethodsOk pl ql s C.A lcid lmid E γr il im iu
        (by rw [HCA]; rfl) Hoff hNx $$ []
    · iframe #
    ihave #Hks := client.srvRunOks_of_slot s E γr [il, im, iu]
        iprop(client.etcdGrpcSlot s E γr ∗ levelTok 0) iprop(True) h1 h2 HL
        (client.etcdLeaseGrantMethods ql E γr) $$ []
    · iframe #
    rw [HCA]
    imod (client.etcd_kv_started_with addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
        sregs (client.etcdLeaseGrantMethods ql E γr)
        Hregs
        (by
          intro m hm
          apply HLr
          simp only [client.etcdLeaseGrantMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl | rfl <;> simp [v3rpc.leaseRegs])
        Hrf Hnd hρ HL) $$ [Hgsn Hlis] with ⟨%γ, Hserv, Hss, -, -, -, -, -, Hle⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb
    simp only [client.etcdLeaseGrantMethods, pbLeaseGrantRequestT, pbLeaseGrantResponseT, pbLeaseLeasesRequestT, pbLeaseLeasesResponseT, pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT]
    icases Hle with ⟨#H1, #H2, #H3, -⟩
    ihave #H1' := (isGrpcRpc_md _ _ _).2 $$ H1
    ihave #H2' := (isGrpcRpc_md _ _ _).2 $$ H2
    ihave #H3' := (isGrpcRpc_md _ _ _).2 $$ H3
    ihave #H2a := isGrpcRpc_leaseLeases_any addr (mvcc.api.mvccLeases E.γ) $$ H2'
    imodintro
    iexists γ
    iframe Hserv Hgo
    isplitl [Hss]
    · iexists pw, ims, is, sregs
      iframe; iframe #
      ipureintro; exact ⟨Hwreg, hRs, hRE⟩
    simp only [etcdLeaseServedAt]
    iunfold etcdLeaseGrantAt
    iunfold client.etcdLeaseReadAt
    iframe #
  | revocable =>
    -- the revocable mode: the lease reads and the live grant
    have hlg : ρ.rd.kv.lg = true := by rw [KVNames.lg_eq, hm]; decide
    ihave #HGL := v3rpc.lessorGrantOkLive_server s E ρ
        iprop(client.etcdRunSlot s E γr ∗ levelTok 0) ⟨hlg, Hoff⟩ (fun q => q.2 = W64 0)
        (fun _ h _ => h) $$ []
    · iframe #
      isplitr
      · iintro !>
        imodintro
        iunfold idCred
        ipureintro; exact Hrb
      iintro !> ⟨HR, Ht⟩
      unfold client.etcdRunSlot
      icases HR with ⟨Hlt, Hst, Hlg, Hrr, Hrd⟩
      iframe Hlt Hrd
      iintro ⟨Hlt, Hrd⟩
      iframe
    ihave #Hlms := client.etcd_leaseGrantLiveMethodsOk pl ql s C.A lcid lmid E γr il im iu
        (by rw [HCA]; rfl) Hoff hNx $$ []
    · iframe #
    ihave #Hks := client.srvRunOks_of_slot s E γr [il, im, iu]
        iprop(client.etcdGrpcSlot s E γr ∗ levelTok 0) iprop(True) h1 h2 HL
        (client.etcdLeaseGrantLiveMethods ql s E γr) $$ []
    · iframe #
    rw [HCA]
    imod (client.etcd_kv_started_with addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
        sregs (client.etcdLeaseGrantLiveMethods ql s E γr)
        Hregs
        (by
          intro m hm
          apply HLr
          simp only [client.etcdLeaseGrantLiveMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl | rfl <;> simp [v3rpc.leaseRegs])
        Hrf Hnd hρ HL) $$ [Hgsn Hlis] with ⟨%γ, Hserv, Hss, -, -, -, -, -, Hle⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb
    simp only [client.etcdLeaseGrantLiveMethods, pbLeaseGrantRequestT, pbLeaseGrantResponseT, pbLeaseLeasesRequestT, pbLeaseLeasesResponseT, pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT]
    icases Hle with ⟨#H1, #H2, #H3, -⟩
    ihave #H1' := (isGrpcRpc_md _ _ _).2 $$ H1
    ihave #H2' := (isGrpcRpc_md _ _ _).2 $$ H2
    ihave #H3' := (isGrpcRpc_md _ _ _).2 $$ H3
    -- the lease reads at the old specs, from the revocable mode's, at the lower bound `0`
    ihave #H1a := isGrpcRpc_leaseTTL_live_any addr (mvcc.api.mvccLeases E.γ) s 0 $$ [$Hlb0 $H1']
    ihave #H2a := isGrpcRpc_leaseLeases_live_any addr (mvcc.api.mvccLeases E.γ) 0 $$ [$Hlb0 $H2']
    imodintro
    iexists γ
    iframe Hserv Hgo
    isplitl [Hss]
    · iexists pw, ims, is, sregs
      iframe; iframe #
      ipureintro; exact ⟨Hwreg, hRs, hRE⟩
    simp only [etcdLeaseServedAt]
    iunfold etcdLeaseGrantLiveAt
    iunfold client.etcdLeaseReadAt
    iframe #

/-- **etcd's lease reads, and by the member's lease mode `m` the KV calls, the grant and the listing
at the lessor's history, or the live grant, registered at the address** (see the file header;
`etcdLeaseServedAt`; the lease-expiry plan's X2, 2026-11-04: by the mode, the KV names' grant flag
its, until then by the flag); as `kv_served`, under `grpcRepliesFit` and the levels `srvLevels`,
with the lease subsystem at the mode (`srvLeaseRd`), and the bounds and the deployment premise
(`leasePeersOk`) the lease reads' server specs take (`threadBound GF ≤ 2 ^ 30 - 1`,
`receiptBound GF ≤ 2 ^ 48`); the runs borrow from the run pools built from `kvServeStocks`
(per-type stage B3: until then the caller gave a thread token for the one gRPC slot). -/
theorem kv_lease_served (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hP : leasePeersOk) (hρ : ρ.rd = γr) (m : lease.Mode)
    (hm : ρ.rd.kv.lm = m) (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E m ∗
        kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> (∃ γ, grpcServeTok gs lis γ) ∗ client.etcdLeaseReadAt addr ∗
        etcdLeaseServedAt m addr s E ρ γr cid mid := by
  iintro H
  imod (kv_lease_served_core s E ρ γr gs lis addr cid mid R Hrb HT Hrf hP hρ m hm HL) $$ H
    with ⟨%γ, Ht, -, -, Hr, Hl⟩
  imodintro
  iframe Hr Hl
  iexists γ
  iexact Ht

/-- **`kv_lease_served`, with the member's `Watch` stream and its refusal freedom** (lease-mono3's
pass 2(c), 2026-11-06; the shape of `client.etcd_kv_started_with`'s post, for `cluster3.StartMember`
in a lease mode, whose `memberServed` keeps the watch stream and `noRefusalAt` in every mode): under
`kv_lease_served`'s premises, the watch server's method set (`hset`, a
`v3rpc.ServerMethodSets`'s `watch_impl`) and the thread bound the watch runs take (`Htb`), the right
to serve, the `GoAttach` resources `grpcUp` holds (`srvGoRes`, back to the caller), the lease reads
and the mode's registrations (`etcdLeaseServedAt`), the watch server `R` with its `Watch` stream
served at the address (`v3rpc.etcd_watch_served_chain`, its runs borrowing from the server's run
pools), and the address refusal-free (`grpcUp_noRefusal`: `etcd_noRefusal`, authentication off). -/
theorem kv_lease_served_watch (s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hP : leasePeersOk) (hρ : ρ.rd = γr) (m : lease.Mode)
    (hm : ρ.rd.kv.lm = m)
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      go_etcd_io.etcd.api.v3.etcdserverpb.WatchServer.ty = true)
    -- (R9, the `lean` merge) the watch path's server facts at `W`, on the store's names
    (W : v3rpc.SrvW GF) (hW : W.γm = E.γ)
    (Htb : threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders) (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E m ∗
        kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ∗ v3rpc.srvWOk W R.wsl v3rpc.wsN ⊢
      |={⊤}=> (∃ γ, grpcServeTok gs lis γ) ∗ srvGoRes s ∗ client.etcdLeaseReadAt addr ∗
        etcdLeaseServedAt m addr s E ρ γr cid mid ∗
        (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
        isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) addr
          go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R)
          (fun md γs Dn => v3rpc.watchStreamSpec γs R W (auth.mdTokenOf md) Dn) ∗
        ⌜noRefusalAt addr⌝ := by
  iintro ⟨#Pv3, #Psrv, #Hreq, #Hrd, Hlr, Hst, Hup, HW⟩
  ihave %Hoff := isServerReq_authOff s E ρ $$ Hreq
  ihave ⟨Hup, %Hnr⟩ := grpcUp_noRefusal s E ρ γr gs lis addr cid mid R Hoff $$ [Hup]
  · iframe Hup; iframe #
  imod (kv_lease_served_core s E ρ γr gs lis addr cid mid R Hrb HT Hrf hP hρ m hm HL)
    $$ [Hlr Hst Hup] with ⟨%γ, Hserv, Hgo, ⟨%pw, %ims, %is, %sregs, %HW, Hss, #Hws, #Hims, #His,
      #Hb, #Hrp⟩, Hr, Hl⟩
  · iframe; iframe #
  obtain ⟨Hwreg, hRs, hRE⟩ := HW
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  imod (v3rpc.etcd_watch_served_chain addr pw R W ims is sregs γ γr (by rw [hRE]; exact hW) Htb HL
    hset Hwreg) $$ [Hss HW] with #Hwst
  · rw [hRs, hRE]
    iframe; iframe #
  imodintro
  iframe Hgo Hr Hl
  iframe #
  isplitl [Hserv]
  · iexists γ; iexact Hserv
  isplitl []
  · ipureintro; exact ⟨hRs, hRE⟩
  ipureintro; exact Hnr

/-- **`kv_lease_served` at `lg = false`** (its post before the lease-grant plan's 2.2): the KV calls
and the lease reads registered at the address. -/
theorem kv_lease_served_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hP : leasePeersOk) (hρ : ρ.rd = γr) (hlg : ρ.rd.kv.lg = false)
    (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E .none ∗
        kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> (∃ γ, grpcServeTok gs lis γ) ∗ etcdKVAt addr E ρ γr cid mid ∗
        client.etcdLeaseReadAt addr := by
  have h := kv_lease_served s E ρ γr gs lis addr cid mid R Hrb HT Hrf hP hρ .none
    (KVNames.lm_of_lg_false hlg) HL
  simp only [etcdLeaseServedAt] at h
  iintro H
  imod h $$ H with ⟨Ht, Hr, Hk⟩
  imodintro
  iframe

end served

end etcdstart
end EtcdGrove
end Perennial
