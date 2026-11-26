/-
`(*watcher).Watch(ctx, key, opts...)` by a client of auth-on members at other machines, at the cluster view,
with the auth row (`notes/etcd-dist-plan.md` §29; an interim trust-boundary axiom until S2's etcd side has the
`Watch` stream entry, as `Watch_dist`: `Proof/.../etcd/dist/WatchOnDist.lean`). Lean-first (no Rocq
counterpart).

`WatchOn_dist.spec` is `Watch_dist.spec` (`WatchDist.lean`) with the auth row of the in-process
`watcher.Watch.spec` (`Spec/go_etcd_io/etcd/client/v3/watcher__Watch.lean`) restated in F7's vocabulary
(`AuthViewDist.lean`), for an auth-on view (`Γ.auth = true`):
* the client's principal is its configured user (`principalOf cfg`, the `cfg` field read-only, no preset
  token), and no context of the watch's stream key carries an issued token (`outTokOkS`, F7's `outTokOk` over
  every metadata of that stream key);
* the in-process gate `V.nm = 1` and bound `n` (member 0's published auth index, `authPubLbM`) become a floor
  at every endpoint (`watchFloorsD eps Γ γR L₀`: the member serving each endpoint has a published auth index
  whose floor is above the caller's requested prefix `L₀`, F7's `authFloorD`), so any member may serve;
* the row's slot, `□ (⌜V.nm = 1⌝ → watchCheckOk …)` in one process, is `watchCheckedD eps Γ γR P L₀ key
  rangeEnd` (`WatchOnViewDist.lean`): the response's stream was created at a member `mid` of the endpoints
  whose check passed for an `AuthInfo` of user `""` or `P`, at the auth history after a committed prefix `L ⊒
  L₀`, on the request's key (`""` read as `"\x00"`) and range end.
A refused watch (a created-then-canceled response with the refusal's reason, or the channel closed) is an
allowed outcome: only a response with events carries the row.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchClientDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchOnViewDist
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
namespace authd

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3
  go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`WatchOn_dist`: `(*watcher).Watch(ctx, key, opts...)` across machines, auth on** (`Watch_dist`'s
statement with the auth row; mirrors `watcher.Watch.spec`, server side `v3rpc.watchSpec` and its create check
`isWatchPermitted`). A watch of a range (any of `isRangeWatchP`'s options) from a revision `rev ≥ 1`, with the
caller's persistent read update of the cluster's KV state, by a client of the endpoints `eps` whose principal is
its configured user (`principalOf cfg`; no context of the watch's stream key sends an issued token, `outTokOkS`),
given a floor above `L₀` at every endpoint's member (`watchFloorsD`), returns an SPSC channel whose `i`-th
response is one firing of the update and a read of that state from the cursor's position `i` to `i + 1`
(`watchStateRespOkP`), whose compaction revision is the cluster's permit (`cmpOkOf Γ.kv`), and which, when it
has events, carries the check of its stream's create (`watchCheckedD`): some member of the endpoints passed it
for the user `""` or the principal's, at the auth history after a committed prefix extending `L₀`. The channel
spans the watcher's reconnections, as `Watch_dist`'s; each re-created stream is checked again, at the member
it reaches. A refused create gives no response with events (the error arm, or the channel's close). -/
abbrev WatchOn_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl w : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (rev : w64) (Q : KVState → IProp GF),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) →
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOkS (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ watchClientAt cl w eps V Γ ∗
      clientF cl go!"cfg" ↦□ cfg ∗ ⌜cfg.Token' = []⌝ ∗ watchFloorsD eps Γ γR L₀ ∗
      EtcdGrove.context.watchCtx ctx ctx_desc ∗ metadata.outMD ctx om ∗ optsAt opts_sl opts ∗
      ⌜(opWatchModel key opts).isRangeWatchP rev = true ∧ ¬ opWatchPanics key opts ∧
        1 ≤ sint.Z rev ∧ watchSizeOk (opWatchModel key opts)⌝ ∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) }}
    (App (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!!
        go!"Watch")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
      isSpsc γw.spsc ch (watchStateElemP Γ.kv γw (opWatchModel key opts).watchNorm Q
        (watchCheckedD eps Γ γR (principalOf cfg) L₀ (opWatchModel key opts).key
          (opWatchModel key opts).base.rangeEnd))
        (fun _ => iprop(True)) ∗
      spscConsumer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListIdxOwn γw.cur 0 (rev - W64 1) }}

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
