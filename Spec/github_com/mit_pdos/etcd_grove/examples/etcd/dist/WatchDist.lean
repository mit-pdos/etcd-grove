/-
`(*watcher).Watch` and `(*watcher).RequestProgress` by a client of members at other machines, at the cluster view
(`notes/etcd-dist-plan.md` §22, §22.6 route (b); trust-boundary axioms until S2's etcd side has the `Watch`
stream entry: `Proof/.../etcd/dist/WatchDist.lean`). Lean-first (no Rocq counterpart).

Each statement is the proved single-process spec with the watcher's environment replaced by the cluster
view:
* `Watch_dist.spec` mirrors `watcher.Watch.spec` (`Spec/go_etcd_io/etcd/client/v3/watcher__Watch.lean`):
  `isClientWatcher V w ∗ ⌜V.kst = γ.st⌝` becomes `watchClientAt cl w eps V Γ` (`WatchClientDist.lean`) with
  `γ := Γ.kv`; the elements' KV names `V.kv` become `Γ.kv`; the auth row (gated on `V.nm = 1`, reading
  member 0's auth tag and server) and its bound `n` are dropped (the row's slot is `True`): the row needs
  per-member auth names in the view (N11). Everything else is verbatim, so the post reads `Γ.kv` only (the
  read update at its state variable `st`, and `cmpOkOf Γ.kv` at its `rlog` and `cret`), which `kvCongr`
  keeps across a restart (§18.2).
* `RequestProgress_dist.spec` mirrors `watcher.RequestProgress.spec`: `isClientWatcher V w` becomes
  `watchClientAt cl w eps V Γ`; the post is the same (`statusErrOk err`, no logical effect: a progress
  notification is a response of the watch's channel, which `Watch_dist`'s elements already describe).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchClientDist
public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.go_etcd_io.etcd.client.v3.WatchCheck
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Proof.context.WatchCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3
  go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`Watch_dist`: `(*watcher).Watch(ctx, key, opts...)` across machines** (mirrors
`watcher.Watch.spec`; server side `v3rpc.watchSpec`, the member's `Watch` stream handler; see the file
header for the differences). A watch of a range (any of `isRangeWatchP`'s: `WithPrefix`, `WithRange`,
`WithFromKey`, `WithRev`, `WithProgressNotify`, `WithCreatedNotify`, `WithPrevKV`) from a revision
`rev ≥ 1`, with the caller's persistent read update of the cluster's KV state, returns an SPSC channel
whose `i`-th response is one firing of the update and a read of that state from the cursor's position
`i` to `i + 1` (`watchStateRespOkP`: an error, a response without events that is not a progress
notification, a progress notification at `p ≥ c` with no event of the range in `(c, p]`, or exactly the
range's events from the cursor to the last one's revision), and whose compaction revision is the
cluster's permit (`cmpOkOf Γ.kv`). The channel spans the watcher's reconnections: a stream that fails
is reopened (at any endpoint the connection picks) and resumed from the cursor, under the same
elements. Any auth mode; no auth row. -/
abbrev Watch_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl w : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (rev : w64) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ watchClientAt cl w eps V Γ ∗
      EtcdGrove.context.watchCtx ctx ctx_desc ∗ metadata.outMD ctx om ∗ optsAt opts_sl opts ∗
      ⌜(opWatchModel key opts).isRangeWatchP rev = true ∧ ¬ opWatchPanics key opts ∧
        1 ≤ sint.Z rev ∧ watchSizeOk (opWatchModel key opts)⌝ ∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) }}
    (App (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!!
        go!"Watch")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
      isSpsc γw.spsc ch (watchStateElemP Γ.kv γw (opWatchModel key opts).watchNorm Q iprop(True))
        (fun _ => iprop(True)) ∗
      spscConsumer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListIdxOwn γw.cur 0 (rev - W64 1) }}

/-- **`RequestProgress_dist`: `(*watcher).RequestProgress(ctx)` across machines** (mirrors
`watcher.RequestProgress.spec`): asks the gRPC stream of `ctx`'s key (opening it if there is none) for a
progress notification, with no logical effect for the caller; returns `nil`, `ctx`'s error, the stream's
close error or `errors.New`'s, each one grpc's `status` accepts. -/
abbrev RequestProgress_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl w : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ watchClientAt cl w eps V Γ ∗
      context.isContext ctx cs ∗ metadata.outgoingCtxOkC ctx }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!!
        go!"RequestProgress")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; statusErrOk err }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
