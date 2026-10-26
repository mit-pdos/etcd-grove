/-
`(*clientv3.watcher).Watch(ctx, key, opts...)` (`client/v3/watch.go`; the watch slice's unit W-C;
D47, 2026-10-26: as repeated reads of etcd's KV state). Lean-first (no Rocq counterpart).

**The triple:** a prefix watch (`opts` the models of the Go options, `optsAt` tying the slice
`opts_sl` of their closures to them; a non-empty key not all `0xff`) from a revision `rev ≥ 1`, on
a client watcher of etcd's KV `γ` (`isKvWatcher`), with the caller's persistent read update of
`γ`'s state (as a linearizable `Get`'s), returns an SPSC channel, with the consumer's side and the
cursor at `rev - 1`, whose `i`-th response is one firing of the update (`watchStateElem`: `□ Q σ`
at some state `σ`) and a read of that state from the cursor's position `i` to `i + 1`
(`watchStateRespOk`): an error, a response without events that is not a progress notification, a
progress notification at `p` (past the cursor: `p ≤ σ.rev` and no event of the range in `(c, p]`),
or events, exactly the range's events of `σ` from the cursor to the last one's revision, as etcd
computes them from its key bucket (`KVState.rangeEvents`: one per change, in order).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
abbrev watcher.Watch.spec : Prop :=
  ∀ (w : Loc) (γ : KVNames) (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF))
    (key : GoString) (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (rev : w64)
    (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isKvWatcher w γ ∗
      context.isContext ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜(opWatchModel key opts).isRangeWatch rev = true ∧ ¬ opWatchPanics key opts ∧
        1 ≤ sint.Z rev ∧ (opWatchModel key opts).key ≠ [] ∧
        (opWatchModel key opts).base.rangeEnd = prefixRangeEnd (opWatchModel key opts).key ∧
        prefixRangeEnd (opWatchModel key opts).key ≠ [W8 0]⌝ ∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>) }}
    (App (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!!
        go!"Watch")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
      isSpsc γw.spsc ch (watchStateElem γw (opWatchModel key opts) Q) (fun _ => iprop(True)) ∗
      spscConsumer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListIdxOwn γw.cur 0 (rev - W64 1) }}

end spec

end EtcdGrove
end Perennial
