/-
**A watch as repeated reads of etcd's KV state** (D46, 2026-10-25; a candidate, for audit before the
watch proofs are ported to it). Lean-first (no Rocq counterpart).

The client's KV specs (`kv.Get`, `kv.Put`, ..., `KVService.lean`) are stated over etcd's KV state
`σ` (`etcdKV γ σ`, `KVState`: the store at the compaction revision and each later revision's
changes, in order). A watch is about the same state: the caller gives a persistent read update of
`σ` (as a linearizable `Get` does), and each response the watch delivers is one firing of it, at a
state `σ` at least as recent as everything the response reports (`□ Q σ`). What the response
reports is computed from `σ` as etcd computes it from its key bucket:

* `KVState.revEvents σ r`: revision `r`'s events, one per change in order, as
  `watchableStoreTxnWrite.End`/`kvsToEvents` make them (`mvcc.evsOfRevM`: a put's event carries
  the key-value the put wrote, a delete's the key with `ModRevision = r`);
* `KVState.rangeEvents σ o lo hi`: the events of the revisions `[lo, hi)` whose key is in the
  watched range, in revision order (`rangeEvents`/`kvsToEvents`' filter; `mvcc.watchEvents`);
* `watchStateRespOk o σ c c' v r`: a response `v` (modelled by `r`), received when the stream is
  at revision `c` and leaving it at `c'`, is an error (position kept), a response without events
  that is not a progress notification (position kept), a progress notification at `p ≤ σ.rev`
  (no event in `(c, p]`; position `max c p`), or events: exactly `rangeEvents σ o (c + 1) (c' + 1)`
  for some `c < c' ≤ σ.rev` (`eventsIs`: each event's type, key, revision and key-value).

`rangeEvents_kvStateOf` ties the events to the server's: at a log's state they are mvcc's watch
events of the log (`mvcc.logEvents`, filtered by the range), so the server's watch proof
(`dispatch_content`) can discharge the contract from the events it sends.

**The candidate triple** (`watcher.Watch.specσ`): a prefix watch (a non-empty key not all `0xff`,
as the current completeness promise, `cplCond`) from a revision `rev ≥ 1`, with the caller's
persistent read update of `γ`'s state, returns an SPSC channel whose `i`-th response satisfies
`watchStateElem`: the update's `□ Q σ` at some state `σ` and `watchStateRespOk` at the positions
`i` and `i + 1` of the watch's cursor (`γw.cur`, from `rev - 1`).

Not yet decided (for the port): `isKvWatcher w γ` here is the client watcher at an environment whose
server runs the KV at `γ`'s state variable, over one member (`isClientWatcher`'s `V.R`); the
multi-member form mirrors `isKv` (D43). `srvNoDupKeys` and `startOk` are not premises: the events
are `σ`'s, whatever a revision's changes are, and the events between the cursor and the reply's
revision are defined whatever the start was.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchFire
public import Proof.go_etcd_io.etcd.client.v3.KVService

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## A client watcher of etcd's KV -/

section resp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A client watcher of etcd's KV `γ`** (persistent; see the file header: one member, its watch
server's apply environment running the KV at `γ`'s state variable). -/
def isKvWatcher (w : Loc) (γ : KVNames) : IProp GF :=
  iprop(∃ (V : client.WEnv GF) (γr : ReadNames), client.isClientWatcher V w ∗
    srvKVInvs V.R.E γr ∗ ⌜γr.kv.st = γ.st⌝)

instance isKvWatcher_persistent (w : Loc) (γ : KVNames) : Persistent (isKvWatcher (GF := GF) w γ) := by
  unfold isKvWatcher; infer_instance

end resp

/-! ## The candidate triple -/

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`w.Watch(ctx, key, opts...)`, as repeated reads of etcd's KV `γ`** (the candidate; see the
file header): a prefix watch (`opts` the models of the Go options, `optsAt` tying the slice `opts_sl`
to them) of a non-empty key not all `0xff`, from a revision `rev ≥ 1`, with the caller's persistent
read update of `γ`'s state, returns a channel whose responses are reads of the state
(`watchStateElem`), with the consumer's side and the cursor at `rev - 1`. -/
abbrev watcher.Watch.specσ : Prop :=
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
