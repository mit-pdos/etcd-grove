/-
The served theorems of the lease service (`kv_lease_served` and its views), over linked results,
moved out of `ServedLease.lean` (2026-11-18) so that its definitions (`etcdLeaseGrantAt`,
`etcdLeaseServedAt`), which other definitions name, import no linked result (CLAUDE.md, "Import
tiers"). See `ServedLease.lean`'s header.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLease
public import Proof.go_etcd_io.etcd.client.v3.LeaseGrantServed
public import Proof.go_etcd_io.etcd.client.v3.LeaseReadServed

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

/-- **`kv_lease_served`, with what the watch service needs** (lease-mono3's pass 2(c),
2026-11-06): its post, and the `GoAttach` resources `grpcUp` holds (`srvGoRes`) and the watch server;
with the watch path's server facts at `W` (`Wo = some W`), the `Watch` stream registered by the start
(phase 7's switch, SW1, 2026-11-24, from `v3rpc.etcd_watch_served_chain`'s run contract, the runs
borrowing from the server's run pools: until then the start gave the stream server
`grpcStreamServerAt`, the watch server's stream chain's contracts and the pools, and the caller
registered the stream). Private: `kv_lease_served` and `kv_lease_served_watch` are its two views. -/
private theorem kv_lease_served_core (Wo : Option (v3rpc.SrvW GF)) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hP : leasePeersOk) (hρ : ρ.rd = γr) (m : lease.Mode)
    (hm : ρ.rd.kv.lm = m) (HL : srvLevels (GF := GF))
    (hWo : ∀ W ∈ Wo, W.γm = E.γ)
    (hset : Wo.isSome → go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      go_etcd_io.etcd.api.v3.etcdserverpb.WatchServer.ty = true)
    (Htb : Wo.isSome → threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders) :
    ([∗list] W ∈ Wo.toList, v3rpc.srvWOk W R.wsl v3rpc.wsN) ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E m ∗
        kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> ∃ (Svc : GrpcSvc GF), grpcServeTok gs lis addr Svc ∗ srvGoRes s ∗
        (∃ pw : Loc, ⌜R.s = s ∧ R.E = E⌝ ∗ v3rpc.isWatchServer pw R ∗
          [∗list] x ∈ Wo.toList.map (fun W => v3rpc.watchMethod pw R W),
            isGrpcStreamMd addr x.name x.Up x.spec) ∗
        client.etcdLeaseReadAt addr ∗ etcdLeaseServedAt m addr s E ρ γr cid mid := by
  iintro ⟨HWo, #Pv3, #Psrv, #Hreq, #Hrd, #Hlr, Hstk, Hup⟩
  iunfold grpcUp at Hup
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, Hgo, Hleft, #Hlu⟩
  obtain ⟨HCA, -, Hregs, Hwreg, hRs, hRE, -, -, Hnd⟩ := HC
  -- the run pools, built from `memberUp`'s stocks
  imod (kvServeStocks_pools s E γr ⊤) $$ Hstk with ⟨#Hrp, #Hb⟩
  -- (phase 7's switch, SW1) the `Watch` stream's run contract, which the start registers, when the
  -- watch path's server facts are given
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hwr : iprop(□ [∗list] x ∈ Wo.toList.map (fun W => v3rpc.watchMethod pw R W),
      grpcStreamRunOk #x.handler x.srv [ims, is] x.Up x.spec ∗ □ ∀ md γ, x.spec md γ (x.dn md γ))
    $$ [HWo]
  · cases Wo with
    | none =>
      iintro !>
      iapply BigSepL.bigSepL_nil.2
      itrivial
    | some W =>
      ihave HW := BigSepL.bigSepL_singleton.1 $$ HWo
      iapply (v3rpc.etcd_watch_served_chain pw R W ims is γr (by rw [hRE]; exact hWo W rfl)
        (Htb rfl) HL (hset rfl))
      rw [hRs, hRE]
      iframe; iframe #
  ihave Hgsn := grpcSrvUp_lis gs lis addr _ _ svcs regs sregs $$ Hgsn
  -- the one gRPC slot, a run's bundle with its level-0 token
  have h1 : srvRunBundle s E γr ⊢
      (client.etcdGrpcSlot s E γr) ∗ iprop(True) := by
    iintro H
    ihave H := (client.etcdGrpcSlot_bundle s E γr).1 $$ H
    iframe
  have h2 : (client.etcdGrpcSlot s E γr) ∗ iprop(True) ⊢
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
  ihave ⟨#Hlrd, #Hpool⟩ := srvLeaseRd_lessorRd s E m $$ Hlr
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
        (client.etcdGrpcSlot s E γr) iprop(True) h1 h2 HL
        (client.etcdLeaseReadMethods ql) $$ []
    · iframe #
    rw [HCA]
    imod (client.etcd_kv_started_with addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
        sregs (client.etcdLeaseReadMethods ql) (Wo.toList.map (fun W => v3rpc.watchMethod pw R W))
        Hregs
        (by
          intro m hm
          apply HLr
          simp only [client.etcdLeaseReadMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl <;> simp [v3rpc.leaseRegs])
        (by
          intro m hm
          simp only [client.etcdLeaseReadMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl <;> simp)
        (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨W, -, rfl⟩ := hx; exact Hwreg)
        (by cases Wo <;> simp)
        Hrf Hnd hρ HL) $$ [Hgsn Hleft] with ⟨Hserv, Hss, #HPut, #HRange, #HDel, #HTxn, #HCmp, Hle⟩
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
    iexists _
    iframe Hserv Hgo
    isplitl [Hss]
    · iexists pw
      isplitr
      · ipureintro; exact ⟨hRs, hRE⟩
      iframe Hws Hss
    simp only [etcdLeaseServedAt]
    iunfold etcdKVAt
    iunfold client.etcdLeaseReadAt
    iframe #
  | mono =>
    -- the monotone mode: the lease reads and the grant at the lessor's history
    have hlg : ρ.rd.kv.lg = true := by rw [KVNames.lg_eq, hm]; decide
    icases srvLeaseRd_srvInv s E .mono (by decide) $$ Hlr with ⟨%on, #Hli⟩
    ihave #HGL := v3rpc.lessorGrantOkLM_server s E ρ iprop(client.etcdRunSlot s E γr ∗ levelTok 0)
        hlg (by rw [hm]; decide) on $$ []
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
    ihave #Hlms := client.etcd_leaseGrantMethodsOk pl ql s C.A lcid lmid E ρ γr il im iu
        (by rw [HCA]; rfl) Hoff hNx $$ []
    · iframe #
    ihave #Hks := client.srvRunOks_of_slot s E γr [il, im, iu]
        (client.etcdGrpcSlot s E γr) iprop(True) h1 h2 HL
        (client.etcdLeaseGrantMethods ql E γr) $$ []
    · iframe #
    rw [HCA]
    imod (client.etcd_kv_started_with addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
        sregs (client.etcdLeaseGrantMethods ql E γr) (Wo.toList.map (fun W => v3rpc.watchMethod pw R W))
        Hregs
        (by
          intro m hm
          apply HLr
          simp only [client.etcdLeaseGrantMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl | rfl <;> simp [v3rpc.leaseRegs])
        (by
          intro m hm
          simp only [client.etcdLeaseGrantMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl | rfl <;> simp)
        (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨W, -, rfl⟩ := hx; exact Hwreg)
        (by cases Wo <;> simp)
        Hrf Hnd hρ HL) $$ [Hgsn Hleft] with ⟨Hserv, Hss, -, -, -, -, -, Hle⟩
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
    iexists _
    iframe Hserv Hgo
    isplitl [Hss]
    · iexists pw
      isplitr
      · ipureintro; exact ⟨hRs, hRE⟩
      iframe Hws Hss
    simp only [etcdLeaseServedAt]
    iunfold etcdLeaseGrantAt
    iunfold client.etcdLeaseReadAt
    iframe #
  | revocable =>
    -- the revocable mode: the lease reads and the live grant
    have hlg : ρ.rd.kv.lg = true := by rw [KVNames.lg_eq, hm]; decide
    icases srvLeaseRd_srvInv s E .revocable (by decide) $$ Hlr with ⟨%on, #Hli⟩
    ihave #HGL := v3rpc.lessorGrantOkLiveM_server s E ρ
        iprop(client.etcdRunSlot s E γr ∗ levelTok 0) (fun q => q.2 = W64 0)
        (fun _ h _ => h) hlg $$ []
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
    ihave #Hlms := client.etcd_leaseGrantLiveMethodsOk pl ql s C.A lcid lmid E ρ γr il im iu
        (by rw [HCA]; rfl) Hoff hNx $$ []
    · iframe #
    ihave #Hks := client.srvRunOks_of_slot s E γr [il, im, iu]
        (client.etcdGrpcSlot s E γr) iprop(True) h1 h2 HL
        (client.etcdLeaseGrantLiveMethods ql s E γr) $$ []
    · iframe #
    rw [HCA]
    imod (client.etcd_kv_started_with addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
        sregs (client.etcdLeaseGrantLiveMethods ql s E γr) (Wo.toList.map (fun W => v3rpc.watchMethod pw R W))
        Hregs
        (by
          intro m hm
          apply HLr
          simp only [client.etcdLeaseGrantLiveMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl | rfl <;> simp [v3rpc.leaseRegs])
        (by
          intro m hm
          simp only [client.etcdLeaseGrantLiveMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl | rfl <;> simp)
        (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨W, -, rfl⟩ := hx; exact Hwreg)
        (by cases Wo <;> simp)
        Hrf Hnd hρ HL) $$ [Hgsn Hleft] with ⟨Hserv, Hss, -, -, -, -, -, Hle⟩
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
    iexists _
    iframe Hserv Hgo
    isplitl [Hss]
    · iexists pw
      isplitr
      · ipureintro; exact ⟨hRs, hRE⟩
      iframe Hws Hss
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
      |={⊤}=> (∃ Svc, grpcServeTok gs lis addr Svc) ∗ client.etcdLeaseReadAt addr ∗
        etcdLeaseServedAt m addr s E ρ γr cid mid := by
  iintro H
  imod (kv_lease_served_core none s E ρ γr gs lis addr cid mid R Hrb HT Hrf hP hρ m hm HL
    (by simp) (fun h => by simp at h) (fun h => by simp at h)) $$ [H]
    with ⟨%Svc, Ht, -, -, Hr, Hl⟩
  · isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    iexact H
  imodintro
  iframe Hr Hl
  iexists Svc
  iexact Ht

/-- **`kv_lease_served`, with the `GoAttach` resources given back** (leaseN, 2026-11-16,
`notes/leaseN-plan.md`): `kv_lease_served`'s post and the member's `srvGoRes` (the thread token it
holds), which a loop serving the members one after another passes on to the next member. -/
theorem kv_lease_served_go (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hP : leasePeersOk) (hρ : ρ.rd = γr) (m : lease.Mode)
    (hm : ρ.rd.kv.lm = m) (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E m ∗
        kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> (∃ Svc, grpcServeTok gs lis addr Svc) ∗ srvGoRes s ∗ client.etcdLeaseReadAt addr ∗
        etcdLeaseServedAt m addr s E ρ γr cid mid := by
  iintro H
  imod (kv_lease_served_core none s E ρ γr gs lis addr cid mid R Hrb HT Hrf hP hρ m hm HL
    (by simp) (fun h => by simp at h) (fun h => by simp at h)) $$ [H]
    with ⟨%Svc, Ht, Hgo, -, Hr, Hl⟩
  · isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    iexact H
  imodintro
  iframe Hgo Hr Hl
  iexists Svc
  iexact Ht

/-- **`kv_lease_served`, with the member's `Watch` stream and its refusal freedom** (lease-mono3's
pass 2(c), 2026-11-06; the shape of `client.etcd_kv_started_with`'s post, for `cluster3.StartMember`
in a lease mode, whose `memberServed` keeps the watch stream and `noRefusalAt` in every mode): under
`kv_lease_served`'s premises, the watch server's method set (`hset`, a
`v3rpc.ServerMethodSets`'s `watch_impl`) and the thread bound the watch runs take (`Htb`), the right
to serve, the `GoAttach` resources `grpcUp` holds (`srvGoRes`, back to the caller), the lease reads
and the mode's registrations (`etcdLeaseServedAt`), the watch server `R` with its `Watch` stream
served at the address (`v3rpc.etcd_watch_served_chain`, its runs borrowing from the server's run
pools; since phase 7's switch, SW1, registered by the start), and the address refusal-free
(`grpcUp_noRefusal`: `etcd_noRefusal`, authentication off). -/
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
      |={⊤}=> (∃ Svc, grpcServeTok gs lis addr Svc) ∗ srvGoRes s ∗ client.etcdLeaseReadAt addr ∗
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
  imod (kv_lease_served_core (some W) s E ρ γr gs lis addr cid mid R Hrb HT Hrf hP hρ m hm HL
    (by intro W' hW'; cases hW'; exact hW) (fun _ => hset) (fun _ => Htb))
    $$ [Hlr Hst Hup HW] with ⟨%Svc, Hserv, Hgo, ⟨%pw, %HRW, #Hws, #Hss⟩, Hr, Hl⟩
  · iframe; iframe #
    iapply BigSepL.bigSepL_singleton.2
    iexact HW
  obtain ⟨hRs, hRE⟩ := HRW
  ihave #Hwst := BigSepL.bigSepL_singleton.1 $$ Hss
  imodintro
  iframe Hgo Hr Hl
  isplitl [Hserv]
  · iexists Svc; iexact Hserv
  isplitl []
  · iexists pw; iexact Hws
  isplitl []
  · ipureintro; exact ⟨hRs, hRE⟩
  isplitl []
  · iexact Hwst
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
      |={⊤}=> (∃ Svc, grpcServeTok gs lis addr Svc) ∗ etcdKVAt addr E ρ γr cid mid ∗
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
