/-
The exported results of etcd's `cache` package, restated at top level, with the trust base of
each printed in the build log (`#print axioms`): what the cache proofs come to, in one file.
Every Go function of the package has a `Spec`/`Proof` pair and a linked result
(`Link.lean`, generated); the results below are the ones a client of the package uses.

* **`New`** (`cache_New`): from a client of etcd for the prefix (`isEtcdClient`, the trust
  boundary about the client) and options, `New` returns either `nil` and an error (a rejected
  configuration) or a cache (`isCacheFields`, every field) with its handles (`cacheHandles`):
  the readers `Get` needs, the slots `Watch` needs, the handles `WaitForNextResync` needs, the
  token `Close` needs; its three loops (resync, watch, progress requests) run.
* **`Get`** (`cache_Get`): the answer is etcd's state at a revision the cache holds
  (`isEtcdKvs`), restricted to the requested range; a linearizable request is at least as fresh
  as etcd was when it started (`cacheGetResult`).
* **`Watch`** (`cache_Watch`) and **its delivery theorem** (`cache_Watch_delivery`): every
  prefix of the responses the caller receives on the returned channel is a `cacheWatchLog`, and
  such a log is, unless the request was rejected, exactly etcd's events under the key range from
  the start revision on, in order, with no gap and no duplicate, each batch certified by etcd's
  step from the previous one (`EtcdStep`), possibly ended by a compaction's cancel after
  everything below the compaction revision.
* `WaitForRevision`, `WaitForNextResync`, `Close`, `Ready`, `WaitReady`, `RequestProgress`: the
  remaining methods of `Cache`.
* **The cache over etcd's client and server** (`cache_end_to_end_client`, unit K3): `New` for a
  client that is etcd's client (a real `*kv`, etcd's client watcher) over etcd's server, the
  trust boundary about the client discharged (`client.isEtcdClient_of_server`): the results
  above then speak of etcd's server (`v3rpc.etcdModelOfServer E`); and for the client
  `clientv3.New` returns (`cache_end_to_end_new`, from `isNewClient`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Link
public import Proof.go_etcd_io.etcd.client.v3.KMClient
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_etcd_io.etcd.client.v3.Results

@[expose] public section

-- `#print axioms` prints the axioms by their full names: shortening each name to the
-- shortest unambiguous one in this environment took most of this module's build (25s of
-- 31s for the server's `txn/Results.lean`).
set_option pp.fullNames true

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `New(client, prefix, opts...)` (`Spec/go_etcd_io/etcd/cache/v3/New.lean`). -/
theorem cache_New : New.spec (GF := GF) (hG := hG) := wp_New

/-- `c.Get(ctx, key, opts...)` (`Spec/go_etcd_io/etcd/cache/v3/Cache__Get.lean`). -/
theorem cache_Get : Cache.Get.spec (GF := GF) (hG := hG) := Cache.wp_Get

/-- `c.Watch(ctx, key, opts...)` (`Spec/go_etcd_io/etcd/cache/v3/Cache__Watch.lean`). -/
theorem cache_Watch : Cache.Watch.spec (GF := GF) (hG := hG) := Cache.wp_Watch

/-- **The `Watch` delivery theorem.** A log `L` of responses received from a `Watch` on
`[key, rangeEnd)` from `sr` (a `cacheWatchLog`: what `cache_Watch`'s channel and
`wp_cacheWatch_receive` give a consumer) is one of:
* the demux's delivery to the watch: its events are exactly the events of etcd's batches `bs`
  whose keys are in the range, in order (no gap, no duplicate), the log in order (`SentOrdered`),
  the batches each of one revision, increasing, and each certified by etcd's step from at most
  the previous one (`certChain (etcdStepCert pfx) p₀ bs`), and for `sr ≠ 0` all at or above
  `sr` with `p₀ < sr` (nothing etcd did from `sr` on is missing);
* such a delivery, complete below a compaction revision `n`, followed by the compaction's
  cancel response;
* the single cancel response of a rejected request. -/
theorem cache_Watch_delivery (pfx key rangeEnd : GoString) (sr : w64) (L : List RespModel) :
    cacheWatchLog (GF := GF) (etcdStepCert pfx) (some (keyPredForRange key rangeEnd)) sr L ⊢
      (∃ (bs : List Batch) (p₀ : Int),
        ⌜eventsOf L = bs.flatten.filter (fun e => keyPredForRange key rangeEnd e.key) ∧
          SentOrdered L ∧ StreamOk bs ∧
          (sr ≠ W64 0 → p₀ < sint.Z sr ∧ ∀ b ∈ bs, sint.Z sr ≤ sint.Z (batchRev b))⌝ ∗
        certChain (etcdStepCert pfx) p₀ bs) ∨
      (∃ (L0 : List RespModel) (n : w64) (bs : List Batch) (p₀ : Int),
        ⌜L = L0 ++ [cancelModel n] ∧
          eventsOf L0 = bs.flatten.filter (fun e => keyPredForRange key rangeEnd e.key) ∧
          SentOrdered L0 ∧ StreamOk bs ∧ (∀ b ∈ bs, sint.Z (batchRev b) < sint.Z n) ∧
          (sr ≠ W64 0 → p₀ < sint.Z sr ∧ ∀ b ∈ bs, sint.Z sr ≤ sint.Z (batchRev b))⌝ ∗
        certChain (etcdStepCert pfx) p₀ bs) ∨
      ⌜∃ r, L = [r] ∧ r.canceled = true ∧ r.events = []⌝ := by
  unfold cacheWatchLog
  iintro (H | ⟨%L0, %n, %HL, H⟩ | %H)
  · ileft
    iapply cacheWatch_delivery pfx key rangeEnd sr L $$ H
  · iright; ileft
    icases cacheWatch_delivery_compacted pfx key rangeEnd sr n L0 $$ H with
      ⟨%bs, %p₀, %Hf, Hc⟩
    iexists L0, n, bs, p₀
    iframe Hc
    ipureintro
    exact ⟨HL, Hf⟩
  · iright; iright
    ipureintro; exact H

/-- `c.WaitForRevision(ctx, rev)`. -/
theorem cache_WaitForRevision : Cache.WaitForRevision.spec (GF := GF) (hG := hG) :=
  Cache.wp_WaitForRevision

/-- `c.WaitForNextResync(ctx)`. -/
theorem cache_WaitForNextResync : Cache.WaitForNextResync.spec (GF := GF) (hG := hG) :=
  Cache.wp_WaitForNextResync

/-- `c.Close()`. -/
theorem cache_Close : Cache.Close.spec (GF := GF) (hG := hG) := Cache.wp_Close

end results

/-! ## etcd's cache over etcd's client (unit K3, 2026-10-18)

`New` of etcd's `cache` package (`cache_New`, `cache/v3/Results.lean`), for a client of etcd that
is etcd's client over etcd's server (`isEtcdClient_of_server`, `CacheClient.lean`): the cache's
contract about its client (`isEtcdClient`) discharged at the server's model, so the cache's
results (`cache_Get`, `cache_Watch`, `cache_Watch_delivery`) are about etcd's server. -/

section cache_client
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [es_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **etcd's cache over etcd's client, end to end** (K3; D48 over the client's specs):
`New(cl, pfx, opts...)` for a client `cl` whose `KV` field is a `*kv` of etcd's KV `γ.kv` (`isKv`,
`kv.Get.spec`'s) and whose `Watcher` field is a client watcher of it (`isKvWatcher`,
`watcher.Watch.spec`'s), for a non-empty prefix not all `0xff`, returns what `New` returns
(`newCacheResult`) at the clients' model of etcd over its KV state (`client.etcdModelOfKV γ`, with
the adapter's invariant `kmInv γ`, `client.kmInv_alloc` from the KV state's half): the cache's
`Get`s and `Watch`es then speak of etcd's KV state. -/
theorem cache_end_to_end_client (cl w api : Loc) (γ : client.KMNames) (dup : Bool)
    (pfx : GoString) (hp : pfx ≠ []) (hff : prefixRangeEnd pfx ≠ [W8 0])
    (hpl : pfx.length ≤ 2 ^ 28) (sl : GoSlice)
    (gs : List (Config → Config)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ context.isClosedchanInit ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        isPkgInit (PROP := IProp GF) pkg_id.context ∗
        clientKVAddr cl ↦□ GoInterface.ok (client.kvIfaceOf api) ∗
        clientWatcherAddr cl ↦□ GoInterface.ok (client.watcherIfaceOf w) ∗
        client.isKv api γ.kv dup ∗ client.isKvWatcher w γ.kv ∗ client.kmInv γ ∗ cfgOptsAt sl gs ∗
        ⌜CfgValid (cfgApply gs defaultConfigVal) → CfgBounded (cfgApply gs defaultConfigVal)⌝ ∗
        ⌜threadBound GF + cacheWgOwedMax ≤ 2 ^ 31⌝ }}
      (App (App (App (Val (@! go_etcd_io.etcd.cache.v3.New)) (Val #cl)) (Val #pfx)) (Val #sl))
    {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
        newCacheResult (EM := client.etcdModelOfKV γ) pfx (cfgApply gs defaultConfigVal) c
          err }} := by
  iintro %Φ ⟨#Pk, #Pcc, #P1, #P2, #P3, #HKV, #HW, #Hkv, #Hw, #Hinv, Hopts, %Hcfg, %Hb⟩ HΦ
  ihave #Hcl := client.isEtcdClient_of_km cl w api γ dup pfx hp hff $$ []
  · iframe #
  iapply (cache_New (EM := client.etcdModelOfKV γ) cl pfx sl gs) $$ [Hopts] HΦ
  iframe #
  iframe
  ipureintro; exact ⟨Hcfg, Hb, hpl⟩

/-- **etcd's cache over `clientv3.New`'s client, end to end** (K3; D48): `cache_end_to_end_client`
for the client `clientv3.New(cfg)` returns (`isNewClient cl [ep] V`, `client_New`'s postcondition):
its `KV` a client of the KV `γ.kv` from the members' registrations at `ep` (`client.isKv_of_regs`),
its `Watcher` etcd's client watcher, a client watcher of `γ.kv` (`isNewClient_watcher`, given the
watch server's facts at `ep`, `watchAddrFacts V`, at `γ.kv`'s state, `V.kst`). -/
theorem cache_end_to_end_new [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (hAs : _root_.Perennial.errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) (cl : Loc) (ep : GoString) (V : client.WEnv GF)
    (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (γ : client.KMNames) (hV : V.addr = ep)
    (hm : V.mem = fun _ => (V.addr, V.R)) (hn : V.nm = 1) (hk : V.kst = γ.kv.st)
    (hst : γr.kv.st = γ.kv.st) (hrb : receiptBound GF ≤ 2 ^ 62)
    (hff : prefixRangeEnd V.pfx ≠ [W8 0]) (hpl : V.pfx.length ≤ 2 ^ 28) (sl : GoSlice)
    (gs : List (Config → Config)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ context.isClosedchanInit ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        isPkgInit (PROP := IProp GF) pkg_id.context ∗ isNewClient cl [ep] V ∗ watchAddrFacts V ∗
        client.kvRegs (client.srvsAt [ep] E γr cid mid) ∗ client.kmInv γ ∗ cfgOptsAt sl gs ∗
        ⌜CfgValid (cfgApply gs defaultConfigVal) → CfgBounded (cfgApply gs defaultConfigVal)⌝ ∗
        ⌜threadBound GF + cacheWgOwedMax ≤ 2 ^ 31⌝ }}
      (App (App (App (Val (@! go_etcd_io.etcd.cache.v3.New)) (Val #cl)) (Val #V.pfx)) (Val #sl))
    {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
        newCacheResult (EM := client.etcdModelOfKV γ) V.pfx (cfgApply gs defaultConfigVal) c
          err }} := by
  iintro %Φ ⟨#Pk, #Pcc, #P1, #P2, #P3, #Hnc, #Hf, #Hrpc, #Hinv, Hopts, %Hcfg, %Hb⟩ HΦ
  ihave ⟨%w, %conn, %wc, %lg, %ics, #HW, #Hw⟩ := isNewClient_watcher context.wp_ErrAny hAs
    cl [ep] V (by rw [hV]) hm hn $$ [$P1 $P2 $P3 $Hnc $Hf]
  ihave #Hnc' := Hnc
  iunfold isNewClient at Hnc'
  icases Hnc' with ⟨-, -, ⟨%api, #HKV, #Hkv⟩, -⟩
  imod (client.isKv_of_regs api [ep] E γr cid mid γ.kv hst hrb) $$ [Hkv Hrpc] with #Hisk
  · iframe #
  ihave #Hkw : client.isKvWatcher w γ.kv $$ []
  · unfold client.isKvWatcher
    iexists { V with conn := conn, ics := ics, wc := wc, lg := lg }
    iframe Hw
    ipureintro; exact hk
  ihave %hp : ⌜V.pfx ≠ []⌝ $$ []
  · iunfold watchAddrFacts at Hf
    icases Hf with ⟨-, -, -, -, %H, -⟩
    ipureintro; exact H.2
  ihave #Hcl := client.isEtcdClient_of_km cl w api γ true V.pfx hp hff $$ []
  · iframe #
  iapply (cache_New (EM := client.etcdModelOfKV γ) cl V.pfx sl gs) $$ [Hopts] HΦ
  iframe #
  iframe
  ipureintro; exact ⟨Hcfg, Hb, hpl⟩

/-- **etcd's server, started for a cache** (the started-server step; as `client.etcd_kv_started`,
the ghost step between `net.Listen` and `go gs.Serve(lis)`): the server `v3rpc.Server` built and a
listener at `addr` (`etcd_kv_started`'s premises) and the watch service's (the `*watchServer` `p`
with its stream registration in `sregs`, the stream chain `[ims, is]`'s contracts, `n` watch run
slots: `etcd_watch_served_chain`'s) give the right to serve `gs` on `lis`, etcd's KV methods
at `addr` (`kvRegs`, the server's request names' read names `γr`), and the watch server's facts at `addr` (`watchAddrFacts V`), given the wire's and the
packages' facts `watchAddrFacts` lists beyond the stream's. With `clientv3.New`'s result at `addr`
these are what `cache_end_to_end_new` takes (and `isServerRead`, `sortNamesOk`, `kvAnyAu`). -/
theorem etcd_cache_served (V : client.WEnv GF) (addr : GoString)
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
    -- (M2, the storage side, review round 2's N1, the approval's item 13) the server off: its store
    -- does not compact, so its watchers' create requests carry the "no compactor" fact
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
        client.kvRegs (client.srvsAt [addr] E γr cid mid) ∗ watchAddrFacts V := by
  iintro ⟨#Pv, #Ps, #Ppb, #Hsrv, #Hsrd, #Hat, #HNR, #Hq, #Hil, #Him, #Hiu, Hgs, Hlis, Hslots,
    #Hws, #Hims, #His, Hwslots, #Hkf, #Heof⟩
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
  ihave #Hlaws := client.watchLaws_srv V hWM hWL Hlink $$ Hkf
  imodintro
  iframe Htok'
  isplitl []
  · iapply client.kvRegs_one
    unfold client.kvRegsAt
    subst hrd
    iframe #
  unfold watchAddrFacts
  rw [hV]
  iframe #
  ipureintro; exact ⟨Hlink, hp⟩

end cache_client

end EtcdGrove
end Perennial

/-! The trust base of the cache's results, printed in the build log. -/
#print axioms Perennial.EtcdGrove.cache_New
#print axioms Perennial.EtcdGrove.cache_Get
#print axioms Perennial.EtcdGrove.cache_Watch
#print axioms Perennial.EtcdGrove.cache_Watch_delivery
#print axioms Perennial.EtcdGrove.cache_WaitForRevision
#print axioms Perennial.EtcdGrove.cache_WaitForNextResync
#print axioms Perennial.EtcdGrove.cache_Close
#print axioms Perennial.EtcdGrove.cache_end_to_end_client
#print axioms Perennial.EtcdGrove.cache_end_to_end_new
#print axioms Perennial.EtcdGrove.etcd_cache_served
