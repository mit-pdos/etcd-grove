/-
**etcd's KV calls and its watch server registered at a served member's address** (k8s 7f-6 E,
2026-11-17). Lean-first (no Rocq counterpart).

`kv_served` (`Served.lean`) with the watch side: from `v3rpc.Server`'s and `Listen`'s results
(`grpcUp`), the member's serving stocks and its serve facts, the right to serve, etcd's KV calls at
the address (`etcdKVAt`), and the member's watch registration (`watchRegAt`): the `Watch` stream at
the address (`v3rpc.etcd_watch_served_chain`), the watch server, and the laws of the server's watch
facts (`srvWOf`, from `srvWOk_of_up`). Unlike `etcd_watch.wk_served_nd` (`watchAddrFacts`, a client
of this one member), it takes no watch condition (`srvOnce`): a cluster's watcher gets it later,
from the instance's invariant (`watchConnFacts_of_members`'s member facts), once the invariant
exists. What a `k`-member start keeps of each member, for a watcher over the members' bridges.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchSrv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Results
public import Proof.go_etcd_io.etcd.client.v3.InvWatch

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

/-- **A member's watch registration at `addr`** (persistent): the `Watch` stream there at its watch
server `R` and the server's watch facts (`srvWOf E γr false`), the watch server, the laws of those
facts, and `R` the server's (`s`, `E`). The watch condition (`srvOnce`) is not here: see the file
header. -/
def watchRegAt (addr : GoString) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) addr
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R)
      (fun md => v3rpc.watchSpec R (srvWOf E γr false) (auth.mdTokenOf md)) ∗
    (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗ client.srvWLaws (srvWOf E γr false) ∗
    ⌜R.s = s ∧ R.E = E⌝)

instance watchRegAt_persistent (addr : GoString) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (R : v3rpc.WSrv GF) : Persistent (watchRegAt addr s E γr R) := by
  unfold watchRegAt; infer_instance

/-- **etcd's KV calls and the watch registration at the address** (see the file header); under
`grpcRepliesFit` (`grpc.start`'s), the mvcc laws `srvWOk_of_up` reads, and v3rpc's method sets. -/
theorem kvWatch_served (Hp : mvcc.api.persistent.law (GF := GF))
    (Hr : mvcc.api.mvccState_reachable.law (GF := GF)) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64) (R : v3rpc.WSrv GF)
    (Hrb : receiptBound GF ≤ 2 ^ 48) (Hrf : grpcRepliesFit) (hρ : ρ.rd = γr)
    (HL : srvLevels (GF := GF)) (Hms : v3rpc.ServerMethodSets)
    (Htb : threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvServeFacts s E cfg ∗
        kvServeStocks s E γr ∗ grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> (∃ γ, grpcServeTok gs lis γ) ∗ etcdKVAt addr E ρ γr cid mid ∗
        watchRegAt addr s E γr R := by
  iintro ⟨#Pv3, #Psrv, #Ppb, #Hreq, #Hrd, #Hsf, Hstk, Hup⟩
  iunfold grpcUp at Hup
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, -, Hlis, -⟩
  obtain ⟨HCA, -, Hregs, Hsreg, hRs, hRE, hRw, -, Hnd⟩ := HC
  imod (kvServeStocks_pools s E γr ⊤) $$ Hstk with ⟨#Hrp, #Hb⟩
  ihave #Hkva := client.kvServerAt_of_is p s C.A cid mid C.n $$ Hkvs
  rw [HCA]
  imod (client.etcd_kv_started addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
      sregs Hregs Hrf Hnd hρ HL) $$ [Hgsn Hlis] with ⟨%γ, Hserv, #Hss, #HPut, #HRange, #HDel, #HTxn, #HCmp⟩
  · iframe; iframe #
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb
  -- the watch path's server facts (R9), then the `Watch` stream at the address
  have hrb62 : receiptBound GF ≤ 2 ^ 62 := by omega
  haveI := v3rpc.srvWOk_persistent Hp (srvWOf E γr false) R.wsl v3rpc.wsN
  ihave #HWok : v3rpc.srvWOk (srvWOf E γr false) R.wsl v3rpc.wsN $$ []
  · rw [hRw]
    iapply (srvWOk_of_up Hp Hr s E γr cfg C hrb62)
    iframe #
  subst hRs hRE
  imod (v3rpc.etcd_watch_served_chain addr pw R (srvWOf R.E γr false) ims is sregs γ γr rfl Htb HL
    Hms.watch_impl Hsreg) $$ [] with #Hst
  · iframe #
  ihave #Hwl := client.srvWLaws_of_ok (srvWOf R.E γr false) R.wsl v3rpc.wsN $$ HWok
  imodintro
  isplitl [Hserv]
  · iexists γ; iexact Hserv
  isplitr
  · iunfold etcdKVAt
    iframe #
  iunfold watchRegAt
  iframe #
  ipureintro; simp

end served

end etcdstart
end EtcdGrove
end Perennial
