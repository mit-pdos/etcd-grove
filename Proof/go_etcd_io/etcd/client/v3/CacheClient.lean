/-
**The cache's client, derived for etcd's client over etcd's server** (unit K3, 2026-10-18).
Lean-first, no Rocq counterpart.

`isEtcdClient_of_server`: a `*clientv3.Client` whose `KV` field is a real `*kv` over a connection
to a gRPC server where etcd's `Range` is registered (`kvObjAt`, `etcd_kv_served`) and whose
`Watcher` field is etcd's client watcher over the same server (`isClientWatcher V w`, `V.R.E = E`)
meets the cache's client contract (`isEtcdClient`, `cache/v3/InvNew.lean`) at the server's model,
for the watcher's prefix: its `Get`s (`isEtcdKVE_of_kv`, any context: the watcher's
`ctxErrClientAllW`), its watches (`isEtcdWatcher_of_watcher`, for a prefix not all `0xff`) and its
progress requests (`isEtcdProgressNotifier_of_watcher`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ServerWatcher
public import Proof.go_etcd_io.etcd.client.v3.ServerKVGet
public import Proof.go_etcd_io.etcd.cache.v3.InvNew

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
updates `kvAnyAu`) and the watcher's (`isClientWatcher`), over the same server (`hE`). -/
theorem isEtcdClient_of_server (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_RP : watcher.RequestProgress.spec (GF := GF) (hG := hG)) (cl : Loc) (V : WEnv GF) (w api : Loc) (addr : GoString) (s : Loc)
    (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (hE : V.R.E = E)
    (hff : prefixRangeEnd V.pfx ≠ [W8 0]) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isServerRead s E γr ∗ kvObjAt api addr ∗
      clientKVAddr cl ↦□ GoInterface.ok (kvIfaceOf api) ∗
      clientWatcherAddr cl ↦□ GoInterface.ok (watcherIfaceOf w) ∗ isClientWatcher V w ∗
      isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
      sortNamesOk ∗ kvAnyAu E γr ⊢
    isEtcdClient (EM := v3rpc.etcdModelOfServer E) cl V.pfx := by
  subst hE
  iintro ⟨#P1, #P2, #P3, #Hsrd, #Hkv, #HKV, #HW, #Hw, #Hrpc, #Hsn, #Hany⟩
  ihave ⟨#Hall, %hp⟩ : iprop(ctxErrClientAll ∗ ⌜V.pfx ≠ []⌝) $$ [Hw]
  · iunfold isClientWatcher at Hw
    icases Hw with ⟨%cs, %vs, -, -, -, -, -, -, -, Hsf, -⟩
    iunfold watchSrvFacts at Hsf
    icases Hsf with ⟨-, Hcf⟩
    iunfold watchConnFacts at Hcf
    icases Hcf with ⟨-, -, -, -, -, -, -, -, -, #Hca, -, %h⟩
    isplitl
    · unfold ctxErrClientAll; iunfold ctxErrClientAllW at Hca; iexact Hca
    ipureintro; exact h.2
  unfold isEtcdClient
  iexists kvIfaceOf api, watcherIfaceOf w
  iframe HKV HW
  isplitr
  · iapply isEtcdKVE_of_kv api addr s V.R.E γr cid mid V.pfx hp
    iframe #
  isplitr
  · iapply isEtcdWatcher_of_watcher wp_Watch V w hff
    iframe #
  iapply isEtcdProgressNotifier_of_watcher wp_RP V w
  iframe #

end proofs

end client
end EtcdGrove
end Perennial
