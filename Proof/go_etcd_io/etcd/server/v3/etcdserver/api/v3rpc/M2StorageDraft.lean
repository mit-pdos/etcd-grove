/-
**M2, the storage side: the watch server's side of F1, drafted** (`notes/m2-storage-plan.md`,
"After review round 1"; `notes/spec-first-study/m2-storage-review-1.md`, F1). Imported by nothing
but the client's Draft (`client/v3/M2StorageDraft.lean`); no `axiom`, no `sorry`.

**Where a client's contribution reaches the handler** (checked for F1): gRPC's stream model
(`Proof/google_golang_org/grpc/InvGrpcStream.lean`) gives a stream method three parameters: the
per-run resource `S` (the server's, from its slot pool), the stream specification `Spec γs Dn`
(fixed by the server at registration, given to both ends at the stream's creation), and the
client's content of each request `Up i m`, which the client gives with `Send` and the handler
gets with `Recv` (`srvStreamIs`; the watch server reads it through `upOk`). A client's `NewStream`
presents nothing. So a client's fact reaches the handler per request, not at the stream's
opening: `watchServer.Watch` calls `NewWatchStream` before any `Recv` (`watch.go:177`). Since a
watcher is registered only by a create request, and a create request already carries a watch
token through `Up` (`watchUp`, D19b), the "no compactor" fact rides with it: the create arm of the
client's content becomes `mvcc.watchTok γ ∗ mvcc.noCompactor γ.st`, which is the drafted store
watch parameters' per-watch token (`mvcc.storeWatchParamsD`'s `T`), so `recvLoop` passes it on as
today (one more conjunct in the pattern). `watchSrvOk`, `isWatchServer`, `grpcCfgOk`,
`v3rpc.Server`, `common.Serve` and `NewServer.specCompact`'s hand-outs stay as they are, mode-free:
a compacting server serves Watch streams, and no client can register a watcher on it (no
`noCompactor` exists there: the authority's other half is the compaction right's).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraft

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Draft of `v3rpc.upOk`** (F1): a create request comes with a watch token of the store and the
"no compactor" fact (`noCompactor`, review round 2's S4'); otherwise as today. -/
def v3rpc.upOkD (γ : mvcc.WsNames) (Up : Nat → v3rpc.WatchReqM → IProp GF) : IProp GF :=
  iprop(□ ∀ (i : Nat) (m : v3rpc.WatchReqM), Up i m -∗ ⌜v3rpc.watchReqOk m⌝ ∗
    (match m with
     | .create _ => iprop(mvcc.watchTok γ ∗ mvcc.noCompactor γ.st)
     | _ => iprop(True)))

instance v3rpc.upOkD_persistent (γ : mvcc.WsNames) (Up : Nat → v3rpc.WatchReqM → IProp GF) :
    Persistent (v3rpc.upOkD γ Up) := by
  unfold v3rpc.upOkD; infer_instance

/-- **Draft of `v3rpc.watchUp`** (F1; the registered content, what the client's `Send` gives): a
create request carries the watch token and the "no compactor" fact. -/
def v3rpc.watchUpD (γ : mvcc.WsNames) (_i : Nat) (m : v3rpc.WatchReqM) : IProp GF :=
  iprop(⌜v3rpc.watchReqOk m⌝ ∗
    (match m with
     | .create _ => iprop(mvcc.watchTok γ ∗ mvcc.noCompactor γ.st)
     | _ => iprop(True)))

/-- The registered content meets the watch server's restrictions and budget (as `upOk_watchUp`). -/
theorem v3rpc.upOkD_watchUpD (γ : mvcc.WsNames) : ⊢ v3rpc.upOkD (GF := GF) γ (v3rpc.watchUpD γ) := by
  unfold v3rpc.upOkD
  iintro !> %i %m H
  unfold v3rpc.watchUpD
  iexact H

/-- **What `recvLoop` hands the mvcc stream with a create** (F1): the create arm is the store
watch parameters' per-watch token. (Draft-only check, review round 2's S6': dropped at the switch,
where `recvLoop`'s pattern is the check.) -/
theorem v3rpc.createArm_T [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (s st : Loc) (γ : mvcc.WsNames) :
    iprop(mvcc.watchTok (GF := GF) γ ∗ mvcc.noCompactor γ.st) ⊢
      (mvcc.storeWatchParamsD s st γ).T :=
  .rfl

/-! ## N1: the watch server's "no compactor" fact (review round 2) -/

/-- **Draft of `watchSrvOk`** (N1; a Draft-only copy: at the switch `isWatchableStore` is redefined
in place and `watchSrvOk`'s text is unchanged): today's, over `isWatchableStoreD`. -/
def v3rpc.watchSrvOkD [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (s : Loc) (E : apply.AEnv GF) (γ : mvcc.WsNames) (wsl : Loc) : IProp GF :=
  iprop(mvcc.isWatchableStoreD wsl E.s γ ∗ ⌜γ.st = E.γ⌝ ∗ v3rpc.raftStatusOk s ∗
    (∃ (st : GoInterface) (cca : Bool) (P : IProp GF) (f : val),
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st E.RD ∗
      □ (⌜E.authMode.isOn = true⌝ → isReqAuthBound st E.RD E.authMode) ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗
      apply.isAuthStore st E.γ P f E.RD E.authMode E.RW) ∗
    v3rpc.watchVars ∗ mvcc.watchTokPool γ ∗ auth.modeTag γ.tag E.authMode)

instance v3rpc.watchSrvOkD_persistent [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (s : Loc) (E : apply.AEnv GF) (γ : mvcc.WsNames) (wsl : Loc) :
    Persistent (v3rpc.watchSrvOkD s E γ wsl) := by
  unfold v3rpc.watchSrvOkD; infer_instance

/-- **Draft of `isWatchServer`** (N1; Draft-only copy, text unchanged at the switch). -/
def v3rpc.isWatchServerD [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (p : Loc) (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(⌜p ≠ null ∧ R.lg ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer go!"lg" p ↦□ R.lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer go!"clusterID" p ↦□ R.cid ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer go!"memberID" p ↦□ R.mid ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer go!"maxRequestBytes" p ↦□ R.mrb ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer go!"sg" p ↦□ v3rpc.srvIface R.s ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer go!"watchable" p ↦□ v3rpc.wsIface R.wsl ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer go!"ag" p ↦□ v3rpc.srvIface R.s ∗
    v3rpc.watchSrvOkD R.s R.E R.γ R.wsl)

instance v3rpc.isWatchServerD_persistent [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (p : Loc) (R : v3rpc.WSrv GF) : Persistent (v3rpc.isWatchServerD p R) := by
  unfold v3rpc.isWatchServerD; infer_instance

/-- **The watch server's "no compactor" fact, given the server's mode** (N1, the law the reviewer
asked for: clients take the fact from the server state they already hold, `isWatchServer`, in
place of a new conjunct of `NewServer.spec`'s post and the examples' bundles). -/
theorem v3rpc.isWatchServerD_noCompactor [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (p : Loc) (R : v3rpc.WSrv GF) (h : ¬ mvcc.kbCmpM R.γ.st.kb) :
    v3rpc.isWatchServerD p R ⊢ mvcc.noCompactor R.γ.st := by
  iintro #H
  iunfold v3rpc.isWatchServerD at H
  icases H with ⟨-, -, -, -, -, -, -, -, Hok⟩
  iunfold v3rpc.watchSrvOkD at Hok
  icases Hok with ⟨#Hws, -⟩
  iapply mvcc.isWatchableStoreD_noCompactor _ _ R.γ h $$ Hws

/-- The watch server's store names are its environment's (a v3rpc law in place of the client's
unfold, `client.watchSrvLink_of_server`). -/
theorem v3rpc.isWatchServerD_link [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (p : Loc) (R : v3rpc.WSrv GF) :
    v3rpc.isWatchServerD p R ⊢ ⌜R.γ.st = R.E.γ⌝ := by
  iintro #H
  iunfold v3rpc.isWatchServerD at H
  icases H with ⟨-, -, -, -, -, -, -, -, Hok⟩
  iunfold v3rpc.watchSrvOkD at Hok
  icases Hok with ⟨-, %h, -⟩
  ipureintro; exact h

/-- **The fact at the server's mode** (N1): the mode read at the server's environment, which is
where the examples know it (`envAgree E E₀` with the stand-in's mode; plan, "After review round 2"). -/
theorem v3rpc.isWatchServerD_noCompactor_env [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (p : Loc) (R : v3rpc.WSrv GF) (h : ¬ mvcc.kbCmpM R.E.γ.kb) :
    v3rpc.isWatchServerD p R ⊢ mvcc.noCompactor R.γ.st := by
  iintro #H
  ihave %hl := v3rpc.isWatchServerD_link p R $$ H
  iapply v3rpc.isWatchServerD_noCompactor p R (by rw [hl]; exact h) $$ H

/-- **Off, the drafted watch server is today's** (a Draft-only bridge, the identity at the in-place
switch of `isWatchableStore`: lets the examples' Draft glue reuse today's client lemmas over
`isWatchServer`, `client.watchSrvLink_of_server` and `watchTokPool_of_server`). -/
theorem v3rpc.isWatchServerD_to [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (p : Loc) (R : v3rpc.WSrv GF) (h : ¬ mvcc.kbCmpM R.E.γ.kb) :
    v3rpc.isWatchServerD p R ⊢ v3rpc.isWatchServer p R := by
  iintro #H
  ihave %hl := v3rpc.isWatchServerD_link p R $$ H
  iunfold v3rpc.isWatchServerD at H
  icases H with ⟨%Hp, #H1, #H2, #H3, #H4, #H5, #H6, #H7, Hok⟩
  iunfold v3rpc.watchSrvOkD at Hok
  icases Hok with ⟨#Hws, #Hrest⟩
  ihave #Hws' := mvcc.isWatchableStoreD_to _ _ R.γ (by rw [hl]; exact h) $$ Hws
  iunfold v3rpc.isWatchServer
  iframe #
  isplitr
  · ipureintro; exact Hp
  iunfold v3rpc.watchSrvOk
  iframe #

/-- **Draft of `etcd_watch_served_chain`'s statement** (`v3rpc/Results.lean`, linked; N1's glue
takes it as a hypothesis): the watch stream registered with the drafted client content
`watchUpD` (a create carries the "no compactor" fact), over the drafted watch server. At the
switch its text is today's (`watchUp`, `isWatchServer` redefined in place); its proof changes in
one place, `watch_streamHandlerOk`'s `upOk_watchUp` (`upOkD_watchUpD`), over `recvLoop`'s pattern
(one more conjunct). -/
abbrev v3rpc.etcd_watch_served_chain.specD [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] : Prop :=
  ∀ (addr : GoString) (p : Loc) (R : v3rpc.WSrv GF) (im is : GoFunc)
    (sregs : List (GoString × val × GoInterface)) (n : Nat),
  go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      etcdserverpb.WatchServer.ty = true →
  (go!"/etcdserverpb.Watch/Watch", (@! etcdserverpb._Watch_Watch_Handler : val),
      interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p) ∈ sregs →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.isWatchServerD p R ∗ srvStreamInterceptorOk im iprop(True) ∗
      srvStreamInterceptorOk is iprop(True) ∗ grpcStreamServerAt addr [im, is] sregs ∗
      ([∗list] _x ∈ List.replicate n (), v3rpc.watchRunSlot R) ⊢
    |={⊤}=> isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) addr
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUpD R.γ)
      (fun γs Dn => v3rpc.watchStreamSpec γs R.γ R.cid R.mid Dn)

end draft

end EtcdGrove
end Perennial
