/-
`(*clientv3.watchGRPCStream).run()` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`w.run()`**, the gRPC watch stream's main goroutine, on a fresh stream (no substream, no
close error, its `resumec` not yet closed (D24: of the generation `0` of `γend`, whose authority it
holds), `respc`'s both sides with no epoch yet (D24), `donec` to be closed by it,
its wait group at `0`): opens the gRPC stream (`newWatchClient`), serves the `Watch` requests of
`reqc` (each a substream with its goroutine, `serveSubstream`, created on the gRPC stream one at a
time: a create sent only for the head of `resuming`; D24: each goroutine a lifetime of its
substream, with its own `donec` and invariant, `LifePrm`), dispatches the stream's responses
(`respc`) to the substreams with the contract's facts, closes the substreams that stop
(`closingc`) and those the server cancels; on a stream error `isHaltErr` retries on (D24),
reconnects (`newWatchClient`, a new epoch at `respc`'s position, the head of `resuming` created on
the new stream); stops when the stream's context is done, the gRPC stream fails with a halting
error or `ErrNoLeader`, or no substream is left, shutting the
substreams down and closing `donec` with its close error (`closeStream`). Its thread token
(`threadTok`) is deposited at each `Add(1)` and replaced by the fresh one of each `go`
(`wgAdder`). -/
abbrev watchGRPCStream.run.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (m0 : Loc) (s0 : GoSlice) (rc : Loc)
    (γrc : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isClientWatcher V G.w ∗ isWGS V G callSl ∗ watcherF G.w go!"callOpts" ↦□ callSl ∗
      wgsF G.wgs go!"substreams" ↦ m0 ∗ ownMap m0 (DFrac.own 1) (∅ : GMap w64 Loc) ∗
      wgsF G.wgs go!"resuming" ↦ s0 ∗ sliceOwn s0 [] ∗
      wgsF G.wgs go!"closeErr" ↦ GoInterface.nil ∗
      wgsF G.wgs go!"resumec" ↦ rc ∗ ownBroadcastChan rc γrc (monoNatLbOwn G.γend 1) .Pending ∗
      monoNatAuthOwn G.γend 1 0 ∗
      sspscConsumer G.γr ([] : List Loc) ∗ sspscProducer G.γr ([] : List Loc) ∗
      monoListAuthOwn G.γep 1 ([] : List EpInfo) ∗
      ownBroadcastChan G.donec G.γdone (closeErrPub G.wgs) .Pending ∗ wgAdder G.wgs ∗ threadTok ∗
      ghostMapAuth G.γws 1 (∅ : GMap Loc Unit) }}
    (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"run")) (Val #()))
  {{ RET #(); threadTok }}

end spec

end EtcdGrove
end Perennial
