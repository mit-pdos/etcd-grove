/-
`(*clientv3.watchGRPCStream).newWatchClient()` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- **`w.newWatchClient()` at its first call** (no substream yet: `substreams` empty, `resuming`
empty; under `noRetryableStreamErr` it is called only once, by `run` at its start): closes the
current `resumec` (no substream listens) and makes a new one that is never closed (`False`), makes
a new empty `substreams` and `resuming`, opens a gRPC watch stream (`openWatchClient`) and, on
success, starts `serveWatchClient` on it with `respc` made an SPSC channel of its responses
(`respcElem`), returning the stream's client end, its sender's token and its specification, and
`respc`'s consumer side; on failure `respc` back and an error grpc's `status` accepts. -/
abbrev watchGRPCStream.newWatchClient.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (m0 : Loc) (s0 : GoSlice) (rc : Loc)
    (γrc γresp : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isWGS V G callSl ∗
      wgsF G.wgs go!"substreams" ↦ m0 ∗ ownMap m0 (DFrac.own 1) (∅ : GMap w64 Loc) ∗
      wgsF G.wgs go!"resuming" ↦ s0 ∗ sliceOwn s0 [] ∗
      wgsF G.wgs go!"resumec" ↦ rc ∗ ownBroadcastChan rc γrc iprop(True) .Pending ∗
      isChan G.respc γresp Loc ∗ ownChan γresp Loc .Idle }}
    (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"newWatchClient")) (Val #()))
  {{ (wc err : GoInterface), RET (PairV #wc #err);
      ∃ (m' : Loc) (s' : GoSlice) (rc' : Loc) (γrc' : ChanNames),
      wgsF G.wgs go!"substreams" ↦ m' ∗ ownMap m' (DFrac.own 1) (∅ : GMap w64 Loc) ∗
      wgsF G.wgs go!"resuming" ↦ s' ∗ sliceOwn s' [] ∗
      wgsF G.wgs go!"resumec" ↦ rc' ∗ ownBroadcastChan rc' γrc' iprop(False) .Pending ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (γs : StreamNames) (Dn : Nat → v3rpc.WatchRespM → IProp GF)
          (cd' : context.ContextDesc (IProp GF)) (γr : SpscNames),
        v3rpc.cliWatchStreamIs wc γs (v3rpc.watchUp V.R.γ) Dn cd' ∗
        cliSendTok (Req := v3rpc.pbWatchRequest) γs [] ∗ v3rpc.watchSpec V.R γs Dn ∗
        isSpsc γr G.respc (respcElem γs Dn) (fun _ => iprop(True)) ∗
        spscConsumer γr ([] : List Loc)) ∨
       (⌜wc = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ statusErrOk err ∗
        isChan G.respc γresp Loc ∗ ownChan γresp Loc .Idle)) }}

end spec

end EtcdGrove
end Perennial
