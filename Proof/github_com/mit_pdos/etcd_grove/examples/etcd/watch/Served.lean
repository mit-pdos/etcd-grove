/-
**etcd's server, started for watchkv** (D23, 2026-10-20). Lean-first (no Rocq counterpart).

`wk_served_nd`: the ghost step between `net.Listen` and `go gs.Serve(l)`, the cache's
`etcd_cache_served` (`Proof/go_etcd_io/etcd/cache/v3/Results.lean`) at one member's registrations
(`kvRegsAt`, what `etcdstart.Writer` takes, where the cache's has `kvRegs`): from `v3rpc.Server`'s
postcondition, the listener and the server's run pools (per-type stage B3; until then caller-chosen
run slots), the right to serve, etcd's KV methods at the
address, and the watch server's facts there (`watchAddrFacts`), given the facts `watchAddrFacts` lists beyond the stream's (the members' KV facts `srvKVFacts`,
`eofOk`), the watch path's server facts at the client's `V.W` (`srvWOk`, R9: the `lean` merge) and
its watch condition (`srvOnce`, in place of mvcc's `watchNoDup`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_watch

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [es_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **etcd's server, started for a watch client, given the watch path's server facts and the
watch condition** (`srvWOk V.W`, `srvOnce V.W`: the store does not compact, watchkv's and
cachekv's, `client.srvOnce_noCmp`; or no revision writes a key twice, `compactkv`'s; watches across a
compaction, W4, 2026-11-01). -/
theorem wk_served_nd (Hp : mvcc.api.persistent.law (GF := GF)) (V : client.WEnv GF) (addr : GoString)
    (gs q p pw s : Loc) (lis : GoInterface) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) (il im iu ims is : GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × GoFunc × GoInterface))
    (hregs : ∀ x ∈ v3rpc.kvRegs q, x ∈ regs) (hV : V.addr = addr) (hE : V.R.E = E) (hs : V.R.s = s)
    (hγm : V.W.γm = V.R.E.γ)
    (hp : V.pfx ≠ []) (hrd : ρ.rd = γr)
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      go_etcd_io.etcd.api.v3.etcdserverpb.WatchServer.ty = true)
    (hwreg : (go!"/etcdserverpb.Watch/Watch",
      (functions go_etcd_io.etcd.api.v3.etcdserverpb._Watch_Watch_Handler [] : GoFunc),
      interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #pw) ∈ sregs)
    -- (W3) the watch contract at the server's model, the watch facts the server's
    (hWM : V.WM = v3rpc.etcdModelOfServer V.R.E γr false) (hWL : V.WL = client.srvWL V.W)
    (hH : V.W.histLb = srvApi.histLb γr false V.R.E.γs)
    (Hrf : grpcRepliesFit) (hnd : ((regs ++ sregs).map Prod.fst).Nodup)
    (Htb : threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders) (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk il (srvLgReader s) Q) ∗
        (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk im iprop(True) Q) ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcSrvNew gs [il, im, iu] [ims, is] svcs regs sregs ∗ netListenerAt lis addr ∗
        srvRevokeBuilt s E ∗ srvRunPool s E γr ∗
        v3rpc.isWatchServer pw V.R ∗ srvStreamInterceptorOk ims iprop(True) ∗
        srvStreamInterceptorWOk is iprop(True) ∗
        client.srvKVFacts V ∗ client.eofOk ∗ v3rpc.srvWOk V.W V.R.wsl v3rpc.wsN ∗
        v3rpc.srvOnce V.W ⊢
      |={⊤}=> (∃ γ, grpcServeTok gs lis γ) ∗
        client.kvRegsAt (⟨addr, E, γr, cid, mid⟩ : client.SrvAt GF) ∗ watchAddrFacts V := by
  haveI := v3rpc.srvWOk_persistent Hp V.W V.R.wsl v3rpc.wsN
  iintro ⟨#Pv, #Ps, #Ppb, #Hsrv, #Hsrd, #Hat, #HNR, #Hq, #Hil, #Him, #Hiu, Hgs, Hlis, #Hb, #Hrp,
    #Hws, #Hims, #His, #Hnd, #Heof, #HW, #Hon⟩
  imod (client.etcd_kv_started addr gs q p s lis E ρ γr cid mid n il im iu ims is svcs regs sregs
    hregs Hrf hnd hrd HL) $$ [Hgs Hlis] with ⟨%γ, Htok', #Hss, #Hput, #Hrange, #Hdel, #Htxn, #Hcmp⟩
  · iframe; iframe #
  imod (v3rpc.etcd_watch_served_chain addr pw V.R V.W ims is sregs γ γr hγm Htb HL hset hwreg) $$ []
    with #Hst
  · rw [hs, hE]
    iframe #
  ihave #Hwl := client.srvWLaws_of_ok V.W V.R.wsl v3rpc.wsN $$ HW
  ihave #Hlaws := client.watchLaws_srv V false γr hWM hWL hH $$ Hwl
  imodintro
  isplitl [Htok']
  · iexists γ; iexact Htok'
  isplitl []
  · unfold client.kvRegsAt
    subst hrd
    iframe #
  unfold watchAddrFacts
  rw [hV]
  iframe #
  ipureintro; exact hp

end served

end etcd_watch
end EtcdGrove
end Perennial
