/-
**What `clientv3.New` returns** (item 5, client construction, 2026-10-17; branch `construct`):
`isNewClient cl eps V`, the client with its connection to the endpoints `eps`, its `KV` and its
`Watcher`; the watch facts of the server at its one endpoint (`watchAddrFacts`; a watch is a stream,
to one address, D27), which `New` does not take (D19f, 2026-10-18): its watcher
is `isClientWatcherCore`, and `isNewClient_watcher` makes it `isClientWatcher` once the facts are
supplied, before the first `Watch`. See `InvClientNew.lean`'s header. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.go_etcd_io.etcd.client.v3.InvWatcherCore
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Proof.go_etcd_io.etcd.client.v3.InvLessor

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
`clientWatchVars`: `watchDescOk_of_init`, `clientWatchVars_of_init`) and `errors.New`'s
(`errorsNewOk`: `errorsNewOk_of`, from the method-set classes of `*errorString`) and every
context's (`ctxErrClientAllW`: `ctxErrClientAllW_of`, from Go's `Err` contract). -/
def watchAddrFacts [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (V : WEnv GF) : IProp GF :=
  iprop(isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) V.addr
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp V.R.γ) (v3rpc.watchSpec V.R) ∗
    mvcc.watchTokPool V.R.γ ∗
    srvLogsSmall V.R ∗ srvNoDupKeys V.R ∗
    eofOk ∗ ⌜V.R.γ.st = V.R.E.γ ∧ V.pfx ≠ []⌝ ∗
    -- (W3) the watch contract's model, from the watcher's logs
    watchLaws V)

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
  have h := congrArg List.length Hs.2.1
  simp at h
  refine ⟨by omega, fun sd hsd => ?_⟩
  have h3 := Hs.2.2
  cases sds with
  | nil => simp at hsd
  | cons x xs =>
    simp at hsd h3
    subst hsd
    exact h3.1

/-- **`client/v3`'s fact gives `watch.go`'s variables** (`clientWatchVars`, `clientv3Init`). -/
theorem clientWatchVars_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ⊢ clientWatchVars := by
  iintro #Hp
  ihave Hi : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  icases Hi with ⟨-, -, -, -, -, -, ⟨%ch, %t, %d, #H1, #H2, #H3⟩, -⟩
  unfold clientWatchVars
  iexists ch, t, d
  iframe #

theorem watchConnFacts_of_addr [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [ErrorStringLeaf] [ErrorStringNoGRPCStatus]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (V : WEnv GF) (conn : Loc) (ics : List GoFunc)
    -- (W3b) a client of one server: its one member
    (hm : V.mem = fun _ => (V.addr, V.R)) (hn : V.nm = 1) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗
      grpcConn (GF := GF) conn [V.addr] ics [] ∗ watchAddrFacts V ⊢
      watchConnFacts { V with conn := conn, ics := ics } := by
  obtain ⟨R, addr, ics0, conn0, wc, pfx, lg, WM, WL, mem, nm⟩ := V
  simp only at hm hn ⊢
  subst hm hn
  unfold watchAddrFacts watchConnFacts watchMemberFacts
  have ha : WEnv.addrs (GF := GF) ⟨R, addr, ics, conn, wc, pfx, lg, WM, WL, fun _ => (addr, R), 1⟩ =
      [addr] := rfl
  have hat : ∀ i, WEnv.atIdx (GF := GF) ⟨R, addr, ics, conn, wc, pfx, lg, WM, WL,
      fun _ => (addr, R), 1⟩ i = ⟨R, addr, ics, conn, wc, pfx, lg, WM, WL, fun _ => (addr, R), 1⟩ :=
    fun _ => rfl
  simp only [ha, hat]
  iintro ⟨#P1, #P2, #P3, #Hc, #H1, #H3, #H5, #H6, #H7, %H11, #H12⟩
  ihave #H8 := client.errorsNewOk_of (GF := GF) hAs
  ihave #H9 := client.ctxErrClientAllW_of wp_ErrAny hAs $$ P3
  ihave #H2 := watchDescOk_of_init $$ P2
  ihave #H10 := clientWatchVars_of_init $$ P1
  iframe #
  isplitr
  · iintro !> %i %hi
    iframe #
    isplitr
    · ipureintro; exact H11.1
    iapply (show watchLaws (GF := GF) ⟨R, addr, ics0, conn0, wc, pfx, lg, WM, WL, fun _ => (addr, R), 1⟩ ⊢
        watchLaws ⟨R, addr, ics, conn, wc, pfx, lg, WM, WL, fun _ => (addr, R), 1⟩ from by
      unfold watchLaws; exact .rfl) $$ H12
  ipureintro
  exact ⟨H11.2, by simp, 0, by decide, by first | rfl | trivial⟩

/-- **What `New` returns** (persistent; see the file header): the client `cl`, connected to the
server at `ep`; its `KV` and `Watcher` over the connection (the watcher's environment `V` at the
connection, its interceptor and some stub and logger), the watcher without the server's facts
(`isClientWatcherCore`; `isNewClient_watcher` adds them); and (item 1, the client lease) its `Lease`,
a `*lessor` over the connection (`lessorAt`). -/
def isNewClient [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (eps : List GoString) (V : WEnv GF) : IProp GF :=
  iprop(clientKVAt cl eps ∗ retryClientOk cl ∗
    (∃ api : Loc, clientF cl go!"KV" ↦□
        interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api ∗
      kvObjAt api eps) ∗
    (∃ (w conn wc lg : Loc) (ics : List GoFunc),
      clientF cl go!"Watcher" ↦□ GoInterface.ok (watcherIfaceOf w) ∗ grpcConn conn eps ics [] ∗
      isClientWatcherCore { V with conn := conn, ics := ics, wc := wc, lg := lg } w) ∗
    -- (item 1, the client lease, 2026-10-18) its `Lease`, a `*lessor` over the connection
    (∃ lp : Loc, clientF cl go!"Lease" ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #lp : GoInterface) ∗
      lessorAt lp eps))

instance isNewClient_persistent [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (eps : List GoString) (V : WEnv GF) : Persistent (isNewClient cl eps V) := by
  unfold isNewClient; infer_instance

/-- **A client configured for one attempt** (persistent; 2026-10-19, D21 M6, D21i:
`MaxUnaryRetries: 1`): its `KV` a `*kv` whose requests are delivered by one attempt (`kvOnce`). -/
def clientKVOnce (cl : Loc) (eps : List GoString) : IProp GF :=
  iprop(∃ api : Loc, clientF cl go!"KV" ↦□
      interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api ∗
    kvOnce api eps)

instance clientKVOnce_persistent (cl : Loc) (eps : List GoString) :
    Persistent (clientKVOnce (GF := GF) cl eps) := by
  unfold clientKVOnce; infer_instance

/-- **The client's watcher, once the watch server's facts are supplied** (D19f): `New`'s client
with `watchAddrFacts V` at its endpoint has a `Watcher` field that is a `*watcher` over the
connection with the server's facts (`isClientWatcher`, what `watcher.Watch`'s spec and
`client_watcher_rangeWatcher` take): the form `isNewClient` had before D19f. -/
theorem isNewClient_watcher [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [ErrorStringLeaf] [ErrorStringNoGRPCStatus]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (cl : Loc) (eps : List GoString) (V : WEnv GF) (hV : eps = [V.addr])
    (hm : V.mem = fun _ => (V.addr, V.R)) (hn : V.nm = 1) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗
      isNewClient cl eps V ∗ watchAddrFacts V ⊢
      ∃ (w conn wc lg : Loc) (ics : List GoFunc),
        clientF cl go!"Watcher" ↦□ GoInterface.ok (watcherIfaceOf w) ∗
        isClientWatcher { V with conn := conn, ics := ics, wc := wc, lg := lg } w := by
  subst hV
  unfold isNewClient
  iintro ⟨#P1, #P2, #P3, ⟨-, -, -, ⟨%w, %conn, %wc, %lg, %ics, #Hw, #Hc, #Hcore⟩, -⟩, #Hf⟩
  iexists w, conn, wc, lg, ics
  iframe Hw
  iapply isClientWatcher_of_core
  iframe Hcore
  iapply (show watchConnFacts (GF := GF) { V with conn := conn, ics := ics } ⊢
      watchConnFacts { V with conn := conn, ics := ics, wc := wc, lg := lg } from by
    unfold watchConnFacts; exact .rfl)
  iapply watchConnFacts_of_addr wp_ErrAny hAs V conn ics hm hn
  iframe P1 P2 P3 Hf
  iexact Hc

end defs

end EtcdGrove
end Perennial
