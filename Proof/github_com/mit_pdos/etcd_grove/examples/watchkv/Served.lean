/-
**etcd's server, started for watchkv** (D23, 2026-10-20). Lean-first (no Rocq counterpart).

`wk_served`: the ghost step between `net.Listen` and `go gs.Serve(l)`, the cache's
`etcd_cache_served` (`Proof/go_etcd_io/etcd/cache/v3/Results.lean`) at one member's registrations
(`kvRegsAt`, what `common.Writer` takes, where the cache's has `kvRegs`): from `v3rpc.Server`'s
postcondition, the listener and the run slots, the right to serve, etcd's KV methods at the
address, and the watch server's facts there (`watchAddrFacts`), given the facts `watchAddrFacts` lists beyond the stream's (the members' KV facts `srvKVFacts`,
`eofOk`). `cert0_of_server`: the watch server's store certifies the start log `[[], []]` (the
store's `isStore`, through `watchSrvOk`).
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
namespace watchkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [es_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **The watch server's store certifies the start log** (`isStore`'s `[[], []]`). -/
theorem cert0_of_server (p : Loc) (R : v3rpc.WSrv GF) :
    v3rpc.isWatchServer (GF := GF) p R ⊢ mvcc.idxCert R.E.γ.idx [[], []] := by
  iintro #H
  iunfold v3rpc.isWatchServer at H
  icases H with ⟨-, -, -, -, -, -, -, -, Hok⟩
  iunfold v3rpc.watchSrvOk at Hok
  icases Hok with ⟨#Hws, %h, -⟩
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  iunfold mvcc.isStore at Hs
  iNamed Hs
  rw [← h]
  iexact Hc0

/-- **etcd's server, started for watchkv** (see the file header). -/
theorem wk_served (V : client.WEnv GF) (addr : GoString)
    (gs q p pw s : Loc) (lis : GoInterface) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) (il im iu ims is : GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × val × GoInterface)) (N nw : Nat)
    (hregs : ∀ x ∈ v3rpc.kvRegs q, x ∈ regs) (hV : V.addr = addr) (hE : V.R.E = E)
    (hp : V.pfx ≠ []) (hrd : ρ.rd = γr)
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      go_etcd_io.etcd.api.v3.etcdserverpb.WatchServer.ty = true)
    (hwreg : (go!"/etcdserverpb.Watch/Watch", (@! go_etcd_io.etcd.api.v3.etcdserverpb._Watch_Watch_Handler : val),
      interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #pw) ∈ sregs)
    -- (W3) the watch contract at the server's model
    (hWM : V.WM = v3rpc.etcdModelOfServer V.R.E) (hWL : V.WL = client.srvWL V.R)
    -- (M2, the storage side, review round 2's N1) the server off (its watchers' "no compactor")
    (hoff : V.R.E.γ.cm = false) :
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
        ([∗list] _x ∈ List.replicate N (), client.etcdGrpcSlot s E γr) ∗
        v3rpc.isWatchServer pw V.R ∗ srvStreamInterceptorOk ims iprop(True) ∗
        srvStreamInterceptorOk is iprop(True) ∗
        ([∗list] _x ∈ List.replicate nw (), v3rpc.watchRunSlot V.R) ∗
        client.srvKVFacts V ∗ client.eofOk ⊢
      |={⊤}=> grpcServeTok gs lis ∗
        client.kvRegsAt (⟨addr, E, γr, cid, mid⟩ : client.SrvAt GF) ∗ watchAddrFacts V := by
  iintro ⟨#Pv, #Ps, #Ppb, #Hsrv, #Hsrd, #Hat, #HNR, #Hq, #Hil, #Him, #Hiu, Hgs, Hlis, Hslots,
    #Hws, #Hims, #His, Hwslots, #Hnd, #Heof⟩
  imod (client.etcd_kv_started addr gs q p s lis E ρ γr cid mid n il im iu ims is svcs regs sregs N
    hregs) $$ [Hgs Hlis Hslots] with ⟨Htok', Hss, #Hput, #Hrange, #Hdel, #Htxn⟩
  · iframe; iframe #
  imod (v3rpc.etcd_watch_served_chain addr pw V.R ims is sregs nw hset hwreg) $$ [Hss Hwslots]
    with #Hst
  · iframe; iframe #
  ihave %Hlink := client.watchSrvLink_of_server pw V.R $$ Hws
  ihave #Htok := client.watchTokPool_of_server pw V.R $$ Hws
  ihave #Hnc := v3rpc.isWatchServer_noCompactor_env pw V.R hoff $$ Hws
  ihave #Hsm : client.srvLogsSmall V.R $$ []
  · iapply client.srvLogsSmall_of_read V.R s γr Hlink
    rw [hE]; iexact Hsrd
  ihave #Hlaws := client.watchLaws_srv V hWM hWL Hlink $$ Hnd
  imodintro
  iframe Htok'
  isplitl []
  · unfold client.kvRegsAt
    subst hrd
    iframe #
  unfold watchAddrFacts
  rw [hV]
  iframe #
  ipureintro; exact ⟨Hlink, hp⟩

end served

end watchkv
end EtcdGrove
end Perennial
