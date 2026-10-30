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
client's content becomes `mvcc.watchTok γ ∗ mvcc.crevFrozen γ.st`, which is the drafted store
watch parameters' per-watch token (`mvcc.storeWatchParamsD`'s `T`), so `recvLoop` passes it on as
today (one more conjunct in the pattern). `watchSrvOk`, `isWatchServer`, `grpcCfgOk`,
`v3rpc.Server`, `common.Serve` and `NewServer.specCompact`'s hand-outs stay as they are, mode-free:
a compacting server serves Watch streams, and no client can register a watcher on it (no
`crevFrozen` exists there: the authority's other half is the compaction right's).
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
"no compactor" fact (`crevFrozen`: the client shows the store frozen); otherwise as today. -/
def v3rpc.upOkD (γ : mvcc.WsNames) (Up : Nat → v3rpc.WatchReqM → IProp GF) : IProp GF :=
  iprop(□ ∀ (i : Nat) (m : v3rpc.WatchReqM), Up i m -∗ ⌜v3rpc.watchReqOk m⌝ ∗
    (match m with
     | .create _ => iprop(mvcc.watchTok γ ∗ mvcc.crevFrozen γ.st)
     | _ => iprop(True)))

instance v3rpc.upOkD_persistent (γ : mvcc.WsNames) (Up : Nat → v3rpc.WatchReqM → IProp GF) :
    Persistent (v3rpc.upOkD γ Up) := by
  unfold v3rpc.upOkD; infer_instance

/-- **Draft of `v3rpc.watchUp`** (F1; the registered content, what the client's `Send` gives): a
create request carries the watch token and the "no compactor" fact. -/
def v3rpc.watchUpD (γ : mvcc.WsNames) (_i : Nat) (m : v3rpc.WatchReqM) : IProp GF :=
  iprop(⌜v3rpc.watchReqOk m⌝ ∗
    (match m with
     | .create _ => iprop(mvcc.watchTok γ ∗ mvcc.crevFrozen γ.st)
     | _ => iprop(True)))

/-- The registered content meets the watch server's restrictions and budget (as `upOk_watchUp`). -/
theorem v3rpc.upOkD_watchUpD (γ : mvcc.WsNames) : ⊢ v3rpc.upOkD (GF := GF) γ (v3rpc.watchUpD γ) := by
  unfold v3rpc.upOkD
  iintro !> %i %m H
  unfold v3rpc.watchUpD
  iexact H

/-- **What `recvLoop` hands the mvcc stream with a create** (F1): the create arm is the store
watch parameters' per-watch token. -/
theorem v3rpc.createArm_T [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (s st : Loc) (γ : mvcc.WsNames) :
    iprop(mvcc.watchTok (GF := GF) γ ∗ mvcc.crevFrozen γ.st) ⊢
      (mvcc.storeWatchParamsD s st γ).T :=
  .rfl

end draft

end EtcdGrove
end Perennial
