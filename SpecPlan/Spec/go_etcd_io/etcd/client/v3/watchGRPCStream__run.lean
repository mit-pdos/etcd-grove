/-
`(*watchGRPCStream).run()`: the stream's main goroutine (forked by `newWatcherGRPCStream`).

**Proof sketch** (what it carries around its loop): `wgsRun s γ who r` and the current stream's
sending half (`wgsSend`, from `newWatchClient.spec`; the receiving half went to
`serveWatchClient`), `cancelSet` and `closing` (local maps: ids it asked to cancel, substreams it
closed the `recvc` of), `cur` (a fragment being reassembled: the **first** fragment's
`wireWatchRespOwn`, the later fragments' events appended to it, `watch.go:596-603`; the receiving
state's `WireSt.frag` is `some (first, evs)` with `cur`'s model the first's with the events `evs`).
The completing response's `wireStep` is stated on `m.toResp evs` for the last message `m`, which
`wireStep` makes agree with the first on the header, the compaction revision and the cancel reason
(and both are neither `Created` nor `Canceled`): so `m.toResp evs` is `cur`'s model's `toResp`, and
`dispatchEvent.spec` gets the `deliverOk` of what it dispatches (verify-round W1). Cases: a `*watchRequest` from `reqc` (its `retc` protocol: a new
substream, `wsOwn` at `WatchPos.init` handed to a forked `serveSubstream` with `wsServe`, the
consumer's `watchChAt` kept for `retc`), sent on the stream if first in `resuming`
(`watchRequest.toPB.spec`, `wireWatchSend_send`: recorded as sent even when `Send` fails, which
`run` only logs); a progress request (forwarded); a response from
`respc` (its `wireStep` facts: `Created` answers `resuming`'s head, `addSubstream.spec`, then
`dispatchEvent.spec`; `Canceled` closes the substream's `recvc` and forgets its id (the fork's fix
of `issues/etcd-watch-resume-stale-canceled-id.md`); a fragment waits; otherwise
`dispatchEvent.spec`, and a cancel for an unknown id); an error from `errc` (`isHaltErr`,
`ContextError` and `ErrNoLeader`: 1c's and W0's specs; else `backoffIfUnavailable.spec`,
`newWatchClient.spec`, `nextResume.spec`); `ctx.Done()`; a stopped substream from `closingc`
(`closeSubstream.spec`, a cancel request). The deferred teardown: close every `recvc` not yet
closed, `joinSubstreams.spec`, `closeSubstream.spec` for each, `wg.Wait()` (the thread-token-backed
wait group), `closeStream.spec` with `wgsDoneTok`. The `watchStep` facts each substream's consumer
gets are `wireStep`'s for the registration of the substream's id, whose position the ghost tie
keeps equal to the substream's: a resume re-creates it from `initReq.rev`, the position's
`done + 1`; a progress of id `-1` holds for every registration, so for every substream
(`broadcastResponse`).

Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
verify-round (A2-provability W1): the fragment case now closes: `wireStep` keeps the first fragment
(`WireSt.frag`) and makes the later ones agree with its header and compaction revision. The
teardown's `closeStream.spec` takes the watcher's handle, which `wgsAt`'s realization keeps
(`∃ c who', watcherHandle w c γ who'`).
**Margin**: mirrors the code.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.WatchInternal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `s.run()`: never panics; ends with the stream torn down. -/
def watchGRPCStream.run.spec : Prop :=
  ∀ (s w : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsAt s w γ who ∗ wgsRun s γ who RunM.init ∗ wgsDoneTok s γ who }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
