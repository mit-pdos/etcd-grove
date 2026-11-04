/-
**etcd's KV calls and lease reads registered at a served member's address** (the closed lease
example, 2026-11-02, `notes/lease-ex-plan.md`). Lean-first (no Rocq counterpart).

`kv_lease_served`: `kv_served`'s ghost step, with the Lease service's reads served too
(`client.etcdLeaseReadAt`: `LeaseTimeToLive`, `LeaseLeases` at etcd's specs), from `grpcUp`'s
Lease service (`grpcLeaseUp`) and the member's lessor reader side (`memberUp`'s `srvLeaseRd`). One
`grpc.serve` serves every method, with one slot: the KV's run resources and a thread token, which
the caller gives (the token of a goroutine that touches no lock, `leasekv`'s `holdToken`: grpc's own
goroutines are not among the threads adequacy counts, so a run's token is one the program forked;
`notes/lease-ex-plan.md`, "The run's thread token"). The lease reads take it with `E.RD` and the
store's reader (`raftLeaseRead_server`'s `E.RD ∗ threadTok`); the KV's runs frame it through.

In a cluster that grants leases (the KV names' `lg`; the lease-grant plan's 2.2, 2026-11-03: one lemma
taking `lg`, which replaced the draft `kv_lease_grant_served`), `LeaseGrant` and `LeaseLeases` are
registered at the specs at the lessor's history instead (`etcdLeaseGrantAt`): a grant's reply carries
its lease's grant (`etcdLeaseGrantSpec`), and a listing lists every grant the caller hands in
(`etcdLeaseLeasesSpec`); the KV's registrations are not passed on (the KV service makes no claim in
that cluster, the plan's Q1). The grant handler calls the server's (`v3rpc.lessorGrantOkL_server`).
`kv_lease_served_false`: the post at `lg = false`, as before.

Why one member's lessor (review S5): the contracts name `E.γ.leases`, this member's, not a
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

/-- **`LeaseGrant` and `LeaseLeases` registered at the specs at the lessor `E.γ.leases`'s
history** (persistent). Per member, not per cluster: `LeaseLeases` is a member-local read (see
the file header). -/
def etcdLeaseGrantAt (addr : GoString) (E : apply.AEnv GF) : IProp GF :=
  iprop(isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant"
      (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E) E.γ.leases) ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpec E.γ.leases))

instance etcdLeaseGrantAt_persistent (addr : GoString) (E : apply.AEnv GF) :
    Persistent (etcdLeaseGrantAt addr E) := by
  unfold etcdLeaseGrantAt; infer_instance

/-- **etcd's lease reads, and the KV calls or (in a cluster that grants leases) the grant and the
listing at the lessor's history, registered at the address** (see the file header); as `kv_served`, under `grpcRepliesFit`, with the lessor's reader side, a thread token for the one gRPC
slot, and the bounds and the deployment premise (`leasePeersOk`) the lease reads' server specs take (`threadBound GF ≤ 2 ^ 30 - 1`, `receiptBound GF ≤ 2 ^ 48`). -/
theorem kv_lease_served (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hP : leasePeersOk) (hρ : ρ.rd = γr) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E ∗ threadTok ∗
        kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> grpcServeTok gs lis ∗ client.etcdLeaseReadAt addr ∗
        (if ρ.rd.kv.lg then etcdLeaseGrantAt addr E else etcdKVAt addr E ρ γr cid mid) := by
  iintro ⟨#Pv3, #Psrv, #Hreq, #Hrd, #Hlr, Htok, ⟨Hlts, Hlgs, Hrds, Hsts, Hrslots, Hbms⟩, Hup⟩
  iunfold grpcUp at Hup
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, -, -, Hlis, #Hlu⟩
  obtain ⟨HCA, -, Hregs, -⟩ := HC
  -- the one gRPC slot, with the thread token
  icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
  icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨-, -, Hrds⟩
  ihave Hslots := client.etcdGrpcSlots_of_started s E γr 1 (64 - 2) 64
      (Int.toNat sync.rwmutex.actualMaxReaders) 64 (by omega) (by omega)
      (by have := sync.actualMaxReaders_ge_2; omega) (by omega)
      $$ [Hlts Hlgs Hrds Hsts Hrslots Hbms]
  · iframe
  icases replicate_take1 _ _ (by omega) $$ Hslots with ⟨Hslot, -⟩
  ihave Hs1 : iprop([∗list] _x ∈ List.replicate 1 (),
      iprop(client.etcdGrpcSlot s E γr ∗ threadTok)) $$ [Hslot Htok]
  · rw [show List.replicate 1 () = [()] from rfl]
    iapply BigSepL.bigSepL_cons.2
    iframe
    iapply BigSepL.bigSepL_nil.2
    itrivial
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
  ihave #HaLL := srvAuthLeaseLb_of_server s E γr (Or.inl hM) $$ []
  · iframe #
  icases v3rpc.srvHeaderFacts_server E.authOn s E ρ $$ HreqM with ⟨%cs, %ms, #Hhf⟩
  iunfold srvLeaseRd at Hlr
  icases Hlr with ⟨#Hlrd, #Hpool⟩
  ihave #HLR := v3rpc.raftLeaseRead_server s E ρ γr E.γ.leases cs ms HT
      (Nat.le_trans Hrb (Nat.pow_le_pow_right (by decide) (by decide))) hP $$ []
  · iframe #
  -- the lower bounds `0`
  ihave #HRI : lease.lessorRdInv E.γ.leases $$ []
  · iunfold srvLessorRd at Hlrd
    icases Hlrd with ⟨%lp, -, #Hinv⟩
    iunfold lease.lessorInv at Hinv
    icases Hinv with ⟨-, -, -, #H⟩
    iexact H
  imod (lease.lessorLb_get E.γ.leases ⊤ (fun _ _ => CoPset.mem_full)) $$ HRI with ⟨%m0, #Hlb⟩
  ihave #Hlb0 := lease.lessorLb_le E.γ.leases 0 (Nat.zero_le _) $$ Hlb
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hpub
  -- the lease reads' meets, at the slot
  iunfold grpcLeaseUp at Hlu
  icases Hlu with ⟨%ql, %pl, %lcid, %lmid, %HLr, #Hql, #Hlat⟩
  ihave #Hkva := client.kvServerAt_of_is p s C.A cid mid C.n $$ Hkvs
  ihave #Hil' := Hil $$ %v3rpc.learnerReqOk
  ihave #Him' := Him $$ %v3rpc.learnerReqOk
  cases hlg : ρ.rd.kv.lg
  · -- the KV calls and the lease reads
    ihave #Hlms := client.etcd_leaseReadMethodsOk pl ql s C.A lcid lmid E γr E.γ.leases il im iu
        (by rw [HCA]; rfl) $$ []
    · iframe #
    rw [HCA]
    imod (client.etcd_kv_started_with addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
        sregs 1 iprop(client.etcdGrpcSlot s E γr ∗ threadTok) threadTok
        (client.etcdLeaseReadMethods ql) (by iintro H; iexact H) (by iintro H; iexact H)
        (by
          simp only [client.etcdKVMethods, client.etcdLeaseReadMethods, List.map, List.cons_append,
            List.nil_append]
          decide)
        Hregs
        (by
          intro m hm
          apply HLr
          simp only [client.etcdLeaseReadMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl <;> simp [v3rpc.leaseRegs])
        Hrf hρ) $$ [Hgsn Hlis Hs1] with ⟨Hserv, -, #HPut, #HRange, #HDel, #HTxn, #HCmp, Hle⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb
    simp only [client.etcdLeaseReadMethods]
    icases Hle with ⟨#H1, #H2, -⟩
    ihave #H1' := (isGrpcRpc_md _ _ _).2 $$ H1
    ihave #H2' := (isGrpcRpc_md _ _ _).2 $$ H2
    imodintro
    iframe Hserv
    simp only [Bool.false_eq_true, ↓reduceIte]
    iunfold etcdKVAt
    iunfold client.etcdLeaseReadAt
    iframe #
  · -- a cluster that grants leases: the lease reads and the grant at the lessor's history
    ihave #HGL := v3rpc.lessorGrantOkL_server s E ρ iprop(client.etcdRunSlot s E γr ∗ threadTok)
        ⟨hlg, Hoff⟩ $$ []
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
        (by rw [HCA]; rfl) Hoff $$ []
    · iframe #
    rw [HCA]
    imod (client.etcd_kv_started_with addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
        sregs 1 iprop(client.etcdGrpcSlot s E γr ∗ threadTok) threadTok
        (client.etcdLeaseGrantMethods ql E) (by iintro H; iexact H) (by iintro H; iexact H)
        (by
          simp only [client.etcdKVMethods, client.etcdLeaseGrantMethods, List.map, List.cons_append,
            List.nil_append]
          decide)
        Hregs
        (by
          intro m hm
          apply HLr
          simp only [client.etcdLeaseGrantMethods, List.mem_cons, List.mem_nil_iff,
            _root_.or_false] at hm
          rcases hm with rfl | rfl | rfl <;> simp [v3rpc.leaseRegs])
        Hrf hρ) $$ [Hgsn Hlis Hs1] with ⟨Hserv, -, -, -, -, -, -, Hle⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb
    simp only [client.etcdLeaseGrantMethods]
    icases Hle with ⟨#H1, #H2, #H3, -⟩
    ihave #H1' := (isGrpcRpc_md _ _ _).2 $$ H1
    ihave #H2' := (isGrpcRpc_md _ _ _).2 $$ H2
    ihave #H3' := (isGrpcRpc_md _ _ _).2 $$ H3
    ihave #H2a := isGrpcRpc_leaseLeases_any addr E.γ.leases $$ H2'
    imodintro
    iframe Hserv
    simp only [↓reduceIte]
    iunfold etcdLeaseGrantAt
    iunfold client.etcdLeaseReadAt
    iframe #

/-- **`kv_lease_served` at `lg = false`** (its post before the lease-grant plan's 2.2): the KV calls
and the lease reads registered at the address. -/
theorem kv_lease_served_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hP : leasePeersOk) (hρ : ρ.rd = γr) (hlg : ρ.rd.kv.lg = false) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E ∗ threadTok ∗
        kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> grpcServeTok gs lis ∗ etcdKVAt addr E ρ γr cid mid ∗
        client.etcdLeaseReadAt addr := by
  have h := kv_lease_served s E ρ γr gs lis addr cid mid R Hrb HT Hrf hP hρ
  simp only [hlg, Bool.false_eq_true, ↓reduceIte] at h
  iintro H
  imod h $$ H with ⟨Ht, Hr, Hk⟩
  imodintro
  iframe

end served

end etcdstart
end EtcdGrove
end Perennial
