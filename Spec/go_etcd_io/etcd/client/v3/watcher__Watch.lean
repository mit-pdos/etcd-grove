/-
`(*clientv3.watcher).Watch(ctx, key, opts...)` (`client/v3/watch.go`; the watch slice's unit W-C;
D47, 2026-10-26: as repeated reads of etcd's KV state). Lean-first (no Rocq counterpart).

**The triple:** a watch of a range (`opts` the models of the Go options, `optsAt` tying the slice
`opts_sl` of their closures to them; G2, 2026-10-30: any range, from-key included; until then a
prefix of a non-empty key) from a revision `rev ≥ 1`, on a client watcher `w` over the environment
`V` whose members run etcd's KV `γ` (`isClientWatcher`, `V.kst = γ.st`; G2: the environment named,
so that the gate below reads it), with the caller's persistent read update of `γ`'s state (as a
linearizable `Get`'s), returns an SPSC channel, with the consumer's side and the cursor at
`rev - 1`, whose `i`-th response is one firing of the update (`watchStateElem`: `□ Q σ` at some
state `σ`) and a read of that state from the cursor's position `i` to `i + 1`
(`watchStateRespOk`): an error, a response without events that is not a progress notification, a
progress notification at `p` (past the cursor: `p ≤ σ.rev` and no event of the range in `(c, p]`),
or events, exactly the range's events of `σ` from the cursor to the last one's revision, as etcd
computes them from its key bucket (`KVState.rangeEvents`: one per change, in order).

**Auth (G2)**: with one member (the gate `V.nm = 1`, a scope restriction: with several, a lagging
member's store checks at its own older auth state), for a caller's bound `n` on the auth store's
published index (`authPubLbM`, needed only for `0 < n`), every response with events carries the
server's check of the watch's create (`watchCheckOk`: on the stream's metadata, for its token, at
states no older than `n`). Margin: the code also ends a refused watch with a canceled response
carrying the refusal's error; the spec says only that no response has events without the row.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.go_etcd_io.etcd.client.v3.WatchCheck

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.server.v3.etcdserver
  client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
abbrev watcher.Watch.spec : Prop :=
  ∀ (w : Loc) (V : WEnv GF) (γ : KVNames) (ctx : GoInterfaceOk)
    (ctx_desc : context.ContextDesc (IProp GF)) (key : GoString) (opts_sl : GoSlice)
    (opts : List (OpFull → OpFull)) (rev : w64) (Q : KVState → IProp GF) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClientWatcher V w ∗ ⌜V.kst = γ.st⌝ ∗
      context.isContext ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜(opWatchModel key opts).isRangeWatch rev = true ∧ ¬ opWatchPanics key opts ∧
        1 ≤ sint.Z rev⌝ ∗
      □ (⌜V.nm = 1 ∧ 0 < n⌝ → auth.authPubLbM (V.mem 0).2.E.authMode n) ∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>) }}
    (App (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!!
        go!"Watch")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
      isSpsc γw.spsc ch (watchStateElem γw (opWatchModel key opts) Q
        iprop(□ (⌜V.nm = 1⌝ → watchCheckOk (V.mem 0).2.γ (V.mem 0).2.s V.conn
          (GoInterface.ok ctx) n (opWatchModel key opts).key (opWatchModel key opts).base.rangeEnd)))
        (fun _ => iprop(True)) ∗
      spscConsumer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListIdxOwn γw.cur 0 (rev - W64 1) }}

end spec

end EtcdGrove
end Perennial
