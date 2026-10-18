/-
**What `clientv3.New` returns** (item 5, client construction, 2026-10-17; branch `construct`):
`isNewClient cl ep V`, the client with its connection, its `KV` and its `Watcher`; the watch facts
of the server at `ep` (`watchAddrFacts`), which `New` does not take (D19f, 2026-10-18): its watcher
is `isClientWatcherCore`, and `isNewClient_watcher` makes it `isClientWatcher` once the facts are
supplied, before the first `Watch`. See `InvClientNew.lean`'s header. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.go_etcd_io.etcd.client.v3.InvWatcherCore

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 client
open go_etcd_io.etcd.cache.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The watch facts of the server at `V.addr`** (persistent): `watchConnFacts V` but the
connection's (`grpcConn`), which the dial gives, and the packages' (`watchDescOk`,
`clientWatchVars`: `watchDescOk_of_init`, `clientWatchVars_of_init`). -/
def watchAddrFacts [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (V : WEnv GF) : IProp GF :=
  iprop(isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) V.addr
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp V.R.γ) (v3rpc.watchSpec V.R) ∗
    mvcc.watchTokPool V.R.γ ∗ noRetryableStreamErr ∗
    srvLogsSmall V.R ∗ srvNoDupKeys V.R ∗
    eofOk ∗ errorsNewOk ∗ ctxErrClientAllW ∗ ⌜V.R.γ.st = V.R.E.γ ∧ V.pfx ≠ []⌝)

instance watchAddrFacts_persistent [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (V : WEnv GF) : Persistent (watchAddrFacts V) := by
  unfold watchAddrFacts; infer_instance

/-- **`etcdserverpb`'s fact gives the `Watch` service's descriptor** (`watchDescOk`: its
`Streams`, the `Watch` stream's; `etcdserverpbDescs`). -/
theorem watchDescOk_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ⊢ v3rpc.watchDescOk := by
  iintro #Hp
  ihave Hi : (go_etcd_io.etcd.cache.v3.etcdserverpbInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  icases Hi with ⟨-, -, -, ⟨%mds, %sds, Hd, %Hs⟩, -⟩
  iunfold pbDescIs at Hd
  icases Hd with ⟨%msl, %ssl, -, -, -, -, #Hst, #Hsds⟩
  unfold v3rpc.watchDescOk
  iexists ssl, sds
  iframe Hst Hsds
  ipureintro
  have h := congrArg List.length Hs.2
  simp at h
  omega

/-- **`client/v3`'s fact gives `watch.go`'s variables** (`clientWatchVars`, `clientv3Init`). -/
theorem clientWatchVars_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ⊢ clientWatchVars := by
  iintro #Hp
  ihave Hi : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  icases Hi with ⟨-, -, -, -, -, -, ⟨%ch, %t, %d, #H1, #H2, #H3⟩⟩
  unfold clientWatchVars
  iexists ch, t, d
  iframe #

theorem watchConnFacts_of_addr [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (V : WEnv GF) (conn : Loc) (ics : List GoFunc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      grpcConn (GF := GF) conn V.addr ics [] ∗ watchAddrFacts V ⊢
      watchConnFacts { V with conn := conn, ics := ics } := by
  unfold watchAddrFacts watchConnFacts
  iintro ⟨#P1, #P2, #Hc, #H1, #H3, #H4, #H5, #H6, #H7, #H8, #H9, %H11⟩
  ihave #H2 := watchDescOk_of_init $$ P2
  ihave #H10 := clientWatchVars_of_init $$ P1
  iframe #
  ipureintro; exact H11

/-- **What `New` returns** (persistent; see the file header): the client `cl`, connected to the
server at `ep`; its `KV` and `Watcher` over the connection (the watcher's environment `V` at the
connection, its interceptor and some stub and logger), the watcher without the server's facts
(`isClientWatcherCore`; `isNewClient_watcher` adds them). -/
def isNewClient [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (ep : GoString) (V : WEnv GF) : IProp GF :=
  iprop(clientKVAt cl ep ∗ retryClientOk cl ∗
    (∃ api : Loc, clientF cl go!"KV" ↦□
        interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api ∗
      kvObjAt api ep) ∗
    (∃ (w conn wc lg : Loc) (ics : List GoFunc),
      clientF cl go!"Watcher" ↦□ GoInterface.ok (watcherIfaceOf w) ∗ grpcConn conn ep ics [] ∗
      isClientWatcherCore { V with conn := conn, ics := ics, wc := wc, lg := lg } w))

instance isNewClient_persistent [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (ep : GoString) (V : WEnv GF) : Persistent (isNewClient cl ep V) := by
  unfold isNewClient; infer_instance

/-- **The client's watcher, once the watch server's facts are supplied** (D19f): `New`'s client
with `watchAddrFacts V` at its endpoint has a `Watcher` field that is a `*watcher` over the
connection with the server's facts (`isClientWatcher`, what `watcher.Watch`'s spec and
`client_watcher_rangeWatcher` take): the form `isNewClient` had before D19f. -/
theorem isNewClient_watcher [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (ep : GoString) (V : WEnv GF) (hV : V.addr = ep) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isNewClient cl ep V ∗ watchAddrFacts V ⊢
      ∃ (w conn wc lg : Loc) (ics : List GoFunc),
        clientF cl go!"Watcher" ↦□ GoInterface.ok (watcherIfaceOf w) ∗
        isClientWatcher { V with conn := conn, ics := ics, wc := wc, lg := lg } w := by
  unfold isNewClient
  iintro ⟨#P1, #P2, ⟨-, -, -, %w, %conn, %wc, %lg, %ics, #Hw, #Hc, #Hcore⟩, #Hf⟩
  iexists w, conn, wc, lg, ics
  iframe Hw
  iapply isClientWatcher_of_core
  iframe Hcore
  iapply (show watchConnFacts (GF := GF) { V with conn := conn, ics := ics } ⊢
      watchConnFacts { V with conn := conn, ics := ics, wc := wc, lg := lg } from by
    unfold watchConnFacts; exact .rfl)
  iapply watchConnFacts_of_addr
  iframe P1 P2 Hf
  rw [hV]
  iexact Hc

end defs

end EtcdGrove
end Perennial
