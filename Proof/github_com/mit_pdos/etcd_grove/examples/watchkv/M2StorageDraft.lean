/-
**M2, the storage side: watchkv's server glue over the Draft** (review round 2's N1; the route in
`notes/m2-storage-plan.md`, "Step 1 on the merged lean"). Imported by nothing; no `axiom`, no
`sorry`. `wk_servedD`: `wk_served` with the watch clients' drafted facts (`watchAddrFactsD`, the
"no compactor" fact a create request carries) from the watch server, given the server off.
At `Main` (`watchkv/Main.lean`, the unfold of `memberUp`): `hoff` is `envAgreeD_off` of the
unfolded `envAgree E E₀` and `E₀.cmp = false`, read off the boot bundle before `newServer`
(`common.memberBootD_cmp`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Served
public import Proof.go_etcd_io.etcd.client.v3.M2StorageDraft

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [es_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **Draft of `wk_served`** (N1, review round 2): the watch server's facts at the address are
`watchAddrFactsD` (the member's "no compactor" fact beside its watch-token pool, the stream's client
content `watchUpD`), given the server's mode, off (`hoff`: from `memberUp`'s `envAgree E E₀`, the
redefinition `envAgreeD`, and the stand-in's `E₀.cmp = false`, `common.memberBootD_cmp`). Proved
against the drafted watch-stream registration (`hchain`, `v3rpc.etcd_watch_served_chain.specD`);
the server's watch facts over the drafted watch server (`isWatchServerD`, today's text at the
switch). The rest as today. -/
theorem wk_servedD
    (hchain : v3rpc.etcd_watch_served_chain.specD (GF := GF) (hG := hG)) (V : client.WEnv GF) (addr : GoString)
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
    -- (N1) the server off
    (hoff : ¬ mvcc.kbCmpM V.R.E.γ.kb) :
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
        v3rpc.isWatchServerD pw V.R ∗ srvStreamInterceptorOk ims iprop(True) ∗
        srvStreamInterceptorOk is iprop(True) ∗
        ([∗list] _x ∈ List.replicate nw (), v3rpc.watchRunSlot V.R) ∗
        client.srvKVFacts V ∗ client.eofOk ⊢
      |={⊤}=> grpcServeTok gs lis ∗
        client.kvRegsAt (⟨addr, E, γr, cid, mid⟩ : client.SrvAt GF) ∗ watchAddrFactsD V := by
  iintro ⟨#Pv, #Ps, #Ppb, #Hsrv, #Hsrd, #Hat, #HNR, #Hq, #Hil, #Him, #Hiu, Hgs, Hlis, Hslots,
    #Hws, #Hims, #His, Hwslots, #Hnd, #Heof⟩
  imod (client.etcd_kv_started addr gs q p s lis E ρ γr cid mid n il im iu ims is svcs regs sregs N
    hregs) $$ [Hgs Hlis Hslots] with ⟨Htok', Hss, #Hput, #Hrange, #Hdel, #Htxn⟩
  · iframe; iframe #
  imod (hchain addr pw V.R ims is sregs nw hset hwreg) $$ [Hss Hwslots]
    with #Hst
  · iframe; iframe #
  ihave #Hnc := v3rpc.isWatchServerD_noCompactor_env pw V.R hoff $$ Hws
  ihave #Hws := v3rpc.isWatchServerD_to pw V.R hoff $$ Hws
  ihave %Hlink := client.watchSrvLink_of_server pw V.R $$ Hws
  ihave #Htok := client.watchTokPool_of_server pw V.R $$ Hws
  ihave #Hsm : client.srvLogsSmall V.R $$ []
  · iapply client.srvLogsSmall_of_read V.R s γr Hlink
    rw [hE]; iexact Hsrd
  ihave #Hlaws := client.watchLaws_srv V hWM hWL Hlink
  imodintro
  iframe Htok'
  isplitl []
  · unfold client.kvRegsAt
    subst hrd
    iframe #
  unfold watchAddrFactsD
  rw [hV]
  iframe #
  ipureintro; exact ⟨Hlink, hp⟩

end draft

end watchkv
end EtcdGrove
end Perennial
