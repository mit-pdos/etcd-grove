/-
**The cache's client, derived for etcd's client over etcd's server** (unit K3, 2026-10-18).
Lean-first, no Rocq counterpart.

`isEtcdClient_of_server`: a `*clientv3.Client` whose `KV` field is a real `*kv` over a connection
to a gRPC server where etcd's `Range` is registered (`kvObjAt`, `etcd_kv_served`) and whose
`Watcher` field is etcd's client watcher over the same server (`isClientWatcher V w`, `V.R.E = E`)
meets the cache's client contract (`isEtcdClient`, `cache/v3/InvNew.lean`) at the server's model,
for the watcher's prefix: its `Get`s (`isEtcdKVE_of_kv_r`, any context: the watcher's
`ctxErrClientAllW`), its watches (`isEtcdWatcher_of_watcher`, for a prefix not all `0xff`) and its
progress requests (`isEtcdProgressNotifier_of_watcher`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ServerWatcher
public import Proof.go_etcd_io.etcd.client.v3.ServerKVGet
public import Proof.go_etcd_io.etcd.cache.v3.InvNew
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3
  go_etcd_io.etcd.server.v3.etcdserver

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [es_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **etcd's client is the cache's** (see the file header): premises the KV's (`Range`'s
registration at `addr`, the server's read side, the sort enumerations' names, the client's read
updates at the ranges, `kvRangeAu`, 2026-10-20; no sort enumerations: the cache's gets do not sort) and the watcher's (`isClientWatcher`), over the same server (`hE`). -/
theorem isEtcdClient_of_server_r (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_RP : watcher.RequestProgress.spec (GF := GF) (hG := hG)) (cl : Loc) (V : WEnv GF) (w api : Loc) (addr : List GoString) (s : Loc)
    (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (hE : V.R.E = E)
    (hWM : V.WM = v3rpc.etcdModelOfServer V.R.E)
    (hff : prefixRangeEnd V.pfx ≠ [W8 0]) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isServerRead s E γr ∗ kvObjAt api addr ∗
      clientKVAddr cl ↦□ GoInterface.ok (kvIfaceOf api) ∗
      clientWatcherAddr cl ↦□ GoInterface.ok (watcherIfaceOf w) ∗ isClientWatcher V w ∗
      isGrpcRpcs addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
      kvRangeAu E γr ⊢
    isEtcdClient (EM := v3rpc.etcdModelOfServer E) cl V.pfx := by
  subst hE
  iintro ⟨#P1, #P2, #P3, #Hsrd, #Hkv, #HKV, #HW, #Hw, #Hrpc, #Hany⟩
  ihave ⟨#Hall, %hp⟩ : iprop(ctxErrClientAll ∗ ⌜V.pfx ≠ []⌝) $$ [Hw]
  · iunfold isClientWatcher at Hw
    icases Hw with ⟨%cs, %vs, -, -, -, -, -, -, -, Hsf, -⟩
    iunfold watchSrvFacts at Hsf
    icases Hsf with ⟨-, Hcf⟩
    iunfold watchConnFacts at Hcf
    icases Hcf with ⟨-, -, -, -, -, -, #Hca, -, %h⟩
    isplitl
    · unfold ctxErrClientAll; iunfold ctxErrClientAllW at Hca; iexact Hca
    ipureintro; exact h.1
  unfold isEtcdClient
  iexists kvIfaceOf api, watcherIfaceOf w
  iframe HKV HW
  isplitr
  · iapply isEtcdKVE_of_kv_r api addr s V.R.E γr cid mid V.pfx hp
    iframe #
  isplitr
  · -- (W3) the watcher's contract is at the server's model
    iapply (show isEtcdWatcher (EM := V.WM) (watcherIfaceOf w) V.pfx ⊢
        isEtcdWatcher (EM := v3rpc.etcdModelOfServer V.R.E) (watcherIfaceOf w) V.pfx from by
      rw [hWM])
    iapply isEtcdWatcher_of_watcher wp_Watch V w hff
    iframe #
  iapply isEtcdProgressNotifier_of_watcher wp_RP V w
  iframe #

/-- **etcd's client is the cache's** (see the file header): premises the KV's (`Range`'s
registration at `addr`, the server's read side, the sort enumerations' names, the client's read
updates `kvAnyAu`) and the watcher's (`isClientWatcher`), over the same server (`hE`). -/
theorem isEtcdClient_of_server (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_RP : watcher.RequestProgress.spec (GF := GF) (hG := hG)) (cl : Loc) (V : WEnv GF) (w api : Loc) (addr : List GoString) (s : Loc)
    (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (hE : V.R.E = E)
    (hWM : V.WM = v3rpc.etcdModelOfServer V.R.E)
    (hff : prefixRangeEnd V.pfx ≠ [W8 0]) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isServerRead s E γr ∗ kvObjAt api addr ∗
      clientKVAddr cl ↦□ GoInterface.ok (kvIfaceOf api) ∗
      clientWatcherAddr cl ↦□ GoInterface.ok (watcherIfaceOf w) ∗ isClientWatcher V w ∗
      isGrpcRpcs addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
      sortNamesOk ∗ kvAnyAu E γr ⊢
    isEtcdClient (EM := v3rpc.etcdModelOfServer E) cl V.pfx := by
  iintro ⟨#P1, #P2, #P3, #Hsrd, #Hkv, #HKV, #HW, #Hw, #Hrpc, #Hsn, #Hany⟩
  ihave #Hr := kvAnyAu_range E γr $$ Hany
  iapply (isEtcdClient_of_server_r wp_Watch wp_RP cl V w api addr s E γr cid mid hE hWM hff)
  iframe #

/-- **`clientv3.New`'s client is the cache's** (`isNewClient`, D19f): its `KV` field the `*kv`
`New` made over the connection to `ep`, its `Watcher` field etcd's client watcher, given the watch
server's facts at `ep` (`watchAddrFacts V`, `isNewClient_watcher`) and the KV's premises at `ep`
(as `isEtcdClient_of_server_r`: the ranges' updates, `kvRangeAu`). -/
theorem isEtcdClient_of_new_r [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [ErrorStringLeaf] [ErrorStringNoGRPCStatus]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_RP : watcher.RequestProgress.spec (GF := GF) (hG := hG)) (cl : Loc) (ep : GoString)
    (V : WEnv GF) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64)
    (hV : V.addr = ep) (hE : V.R.E = E)
    (hWM : V.WM = v3rpc.etcdModelOfServer V.R.E)
    (hm : V.mem = fun _ => (V.addr, V.R)) (hn : V.nm = 1) (hff : prefixRangeEnd V.pfx ≠ [W8 0]) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isNewClient cl [ep] V ∗ watchAddrFacts V ∗
      isServerRead s E γr ∗ isGrpcRpc ep go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
      kvRangeAu E γr ⊢
    isEtcdClient (EM := v3rpc.etcdModelOfServer E) cl V.pfx := by
  iintro ⟨#P1, #P2, #P3, #Hnc, #Hf, #Hsrd, #Hrpc0, #Hany⟩
  ihave #Hrpc := (isGrpcRpcs_singleton ep _ _).1 $$ Hrpc0
  ihave ⟨%w, %conn, %wc, %lg, %ics, #HW, #Hw⟩ := isNewClient_watcher wp_ErrAny hAs cl [ep] V
    (by rw [hV]) hm hn $$ [$P1 $P2 $P3 $Hnc $Hf]
  ihave #Hnc' := Hnc
  iunfold isNewClient at Hnc'
  icases Hnc' with ⟨-, -, ⟨%api, #HKV, #Hkv⟩, -⟩
  iapply (isEtcdClient_of_server_r wp_Watch wp_RP cl
    { V with conn := conn, ics := ics, wc := wc, lg := lg } w api [ep] s E γr cid mid hE hWM hff)
  iframe #

/-- **`clientv3.New`'s client is the cache's** (`isNewClient`, D19f): its `KV` field the `*kv`
`New` made over the connection to `ep`, its `Watcher` field etcd's client watcher, given the watch
server's facts at `ep` (`watchAddrFacts V`, `isNewClient_watcher`) and the KV's premises at `ep`
(as `isEtcdClient_of_server`). -/
theorem isEtcdClient_of_new [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [ErrorStringLeaf] [ErrorStringNoGRPCStatus]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_RP : watcher.RequestProgress.spec (GF := GF) (hG := hG)) (cl : Loc) (ep : GoString)
    (V : WEnv GF) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64)
    (hV : V.addr = ep) (hE : V.R.E = E)
    (hWM : V.WM = v3rpc.etcdModelOfServer V.R.E)
    (hm : V.mem = fun _ => (V.addr, V.R)) (hn : V.nm = 1) (hff : prefixRangeEnd V.pfx ≠ [W8 0]) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isNewClient cl [ep] V ∗ watchAddrFacts V ∗
      isServerRead s E γr ∗ isGrpcRpc ep go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
      sortNamesOk ∗ kvAnyAu E γr ⊢
    isEtcdClient (EM := v3rpc.etcdModelOfServer E) cl V.pfx := by
  iintro ⟨#P1, #P2, #P3, #Hnc, #Hf, #Hsrd, #Hrpc, #Hsn, #Hany⟩
  ihave #Hr := kvAnyAu_range E γr $$ Hany
  iapply (isEtcdClient_of_new_r wp_ErrAny hAs wp_Watch wp_RP cl ep V s E γr cid mid hV hE hWM hm hn hff)
  iframe #

end proofs

end client
end EtcdGrove
end Perennial
