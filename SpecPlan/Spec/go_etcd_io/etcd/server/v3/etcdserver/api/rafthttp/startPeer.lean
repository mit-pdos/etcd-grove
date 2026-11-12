/-
## `startPeer(t, urls, peerID, fs)`

**Users.** `Transport.AddPeer`.

**Proof sketch.** `newPeerStatus`, `newURLPicker` (`pickerAt`), the pipeline literal (`pipeFresh`) and `pipeline.start`, two `startStreamWriter`s, `newSnapshotSender`, `recvc`/`propc` (`recvChanAt`: every value a fresh message with `recvd`), `context.WithCancel(Background)`, two goroutines each receiving from one channel and calling `Raft.Process` (`raftOk`, with the goroutine's own thread token), two `streamReader` literals (`srFresh`, `rate.NewLimiter`: trust) and their `start`. The stop right holds the writers', pipeline's, sender's and readers' stop rights and the loops' stop channel. `types.ID`'s `String()` on an addressable `ID` (log fields, headers) is 1c's `Types.ID.String_ptr.spec` (Goose's pointer receiver).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. The loops' `R`s (eight per peer, from `raftPool`) are gone: each goroutine has its thread token from `Fork`. verify-round (second pass): the sketch cites `Types.ID.String_ptr.spec`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) **Starts peer `pid`** of the transport of `lid`: its pipeline, two stream writers, two stream readers, snapshot sender and two `Process` loops. -/
def startPeer.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid pid : w64) (urls : GoSlice) (hs : List GoString) (fs : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ Types.urlsAt urls hs ∗ ⌜hs ≠ []⌝ ∗ ([∗list] a ∈ hs, peerAddr ν a) ∗ followerStatsOk fs }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.startPeer)) (Val #t)) (Val #urls)) (Val #pid)) (Val #fs))
  {{ (p : Loc), RET #p; peerAt p ν lid pid ∗ peerStopRight p }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
