/-
`(*clientv3.watchGRPCStream).serveSubstream(ws, resumec)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- **`w.serveSubstream(ws, resumec)`**, the goroutine of the watch `P` (its substream `ws`, fresh:
not closing, an empty buffer, a buffer logger or none, half the request's `rev` field and its
`retc` field with the caller's resources): receives `run`'s responses on `recvc` (the consumer's
side; the dispatch cursor's first position `rev - 1`), sends its channel on `retc` at the created
response (and publishes it if asked), buffers the others and publishes them on `outc` (the
producer's side, the cursor `γ.cur` from `rev - 1`) in order, each with the contract's facts
(`rangeWatchElem`, from `recvElem`'s), until `recvc` is closed or the stream's or the watch's
context is done (`resumec` is never closed: `False`); then closes its `donec`, hands what it holds
to `run` on `closingc` (`closingP`) and signals the wait group, which gives it the thread token it
exits with (`wgDone`; `run` keeps the fresh token of the `go` statement). -/
abbrev watchGRPCStream.serveSubstream.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (P : WsPrm GF) (b0 : GoSlice) (bl : Loc)
    (t0 : _root_.Perennial.time.Time) (rc : Loc) (γrc : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isWGS V G callSl ∗
      wsIs V P ∗
      wsF P.ws go!"closing" ↦ false ∗ wsF P.ws go!"buf" ↦ b0 ∗ sliceOwn b0 [] ∗
      wsF P.ws go!"bufLogger" ↦ bl ∗ bufLogOk P.ws bl ∗ wsF P.ws go!"bufWaitStartTime" ↦ t0 ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} P.rev ∗ wsReqF P.ws go!"retc" ↦ P.retc ∗
      retcRes P ∗
      spscProducer P.γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListAuthOwn P.γ.cur 1 [P.rev - W64 1] ∗
      spscConsumer P.γr ([] : List Loc) ∗ monoListIdxOwn P.γhi 0 (P.rev - W64 1) ∗
      ownBroadcastChan rc γrc iprop(False) .Unknown ∗
      ownBroadcastChan P.donec P.γdn (dghostVar P.γx DFrac.discard true) .Pending ∗
      dghostVar P.γx (DFrac.own 1) false ∗ wgDone G.wgs ∗
      ghostMapElem G.γws P.ws (DFrac.own 1) () }}
    (App (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"serveSubstream")) (Val #P.ws)) (Val #rc))
  {{ RET #(); threadTok }}

end spec

end EtcdGrove
end Perennial
