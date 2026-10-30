/-
`(*clientv3.watchGRPCStream).newWatchClient()` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.go_etcd_io.etcd.client.v3.WatchRun

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`w.newWatchClient()`** (D25: `run`'s start and every reconnection): closes the current
`resumec` (its generation `n` ends, `γend`; every goroutine of a substream resumes or has stopped)
and makes a new one of the next generation; waits for the substreams of `substreams` and
`resuming` (`joinSubstreams`) and takes what their goroutines left; resets their ids and queues
them all, the stopped ones too, in `resuming` (`l'`, the nils dropped), with a new empty
`substreams`; while it opens a gRPC watch stream (`openWatchClient`), closes the substreams whose
watch's context is done (`waitCancelSubstreams`); restarts a goroutine for each substream not
stopped (`serveSubstream`, from its resume revision). `run`'s knowledge (`S`, the substreams `U`)
becomes the reconnection's (`RunSt.reconnect`, every substream's phase `WPh.recon`: queued,
re-created on any next stream `γs'` from its resume revision). On success it starts
`serveWatchClient` on the stream as `run`'s next epoch (D25: appended to `G.γep`, from `respc`'s
position `sent.length`, with `respc`'s producer side) and returns the stream's client end, its
sender's token and its specification; on failure `respc`'s producer side back and an error grpc's
`status` accepts. -/
abbrev watchGRPCStream.newWatchClient.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (m0 : Loc) (s0 : GoSlice) (rc : Loc)
    (γrc : ChanNames) (n : Nat) (sent : List Loc) (eps : List EpInfo) (γs : StreamNames)
    (S : RunSt) (U : GMap Loc Unit),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isWGS V G callSl ∗
      wgsF G.wgs go!"substreams" ↦ m0 ∗ ownMap m0 (DFrac.own 1) S.M ∗
      wgsF G.wgs go!"resuming" ↦ s0 ∗ sliceOwn s0 S.l ∗
      wgsF G.wgs go!"resumec" ↦ rc ∗
      ownBroadcastChan rc γrc (monoNatLbOwn G.γend (n + 1)) .Pending ∗ monoNatAuthOwn G.γend 1 n ∗
      sspscProducer G.γr sent ∗ monoListAuthOwn G.γep 1 eps ∗
      ⌜gOk S U⌝ ∗ ghostMapAuth G.γws 1 U ∗ ([∗map] ws ↦ _u ∈ U, wsElem V G n γs S ws) ∗
      wgAdder G.wgs ∗ threadTok }}
    (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"newWatchClient")) (Val #()))
  {{ (wc err : GoInterface), RET (PairV #wc #err);
      ∃ (m' : Loc) (s' : GoSlice) (rc' : Loc) (γrc' : ChanNames) (l' : List Loc),
      wgsF G.wgs go!"substreams" ↦ m' ∗ ownMap m' (DFrac.own 1) (∅ : GMap w64 Loc) ∗
      wgsF G.wgs go!"resuming" ↦ s' ∗ sliceOwn s' l' ∗
      wgsF G.wgs go!"resumec" ↦ rc' ∗
      ownBroadcastChan rc' γrc' (monoNatLbOwn G.γend (n + 2)) .Pending ∗
      monoNatAuthOwn G.γend 1 (n + 1) ∗
      ⌜gOk (S.reconnect l') U⌝ ∗ ghostMapAuth G.γws 1 U ∗
      -- (W3b) on any next stream, at any member (a queued substream reads no member)
      (∀ (γs' : StreamNames) (i' : Nat),
        [∗map] ws ↦ _u ∈ U, wsElem (V.atIdx i') G (n + 1) γs' (S.reconnect l') ws) ∗
      wgAdder G.wgs ∗ threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (i : Nat) (γs' : StreamNames)
          (Dn : Nat → v3rpc.WatchRespM → IProp GF) (cd' : context.ContextDesc (IProp GF))
          (γc : GName) (md : GrpcMd),
        -- (W3b) the stream at the member `i`, which its epoch records; (G2) opened with the
        -- metadata `md` an attempt on the connection delivered for the stream's context, its
        -- specification at `md`'s token, which the epoch records too
        ⌜i < V.nm ∧ clientAttemptMd V.conn (GoInterface.ok G.ctx) md⌝ ∗
        v3rpc.cliWatchStreamIs wc γs' (v3rpc.watchUp (V.mem i).2) Dn cd' ∗
        cliSendTok (Req := v3rpc.pbWatchRequest) γs' [] ∗
        v3rpc.watchSpec (V.mem i).2 (auth.mdTokenOf md) γs' Dn ∗
        monoListAuthOwn G.γep 1
          (eps ++ [((γs', sent.length, γc, i, auth.mdTokenOf md) : EpInfo)])) ∨
       (⌜wc = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ statusErrOk err ∗
        sspscProducer G.γr sent ∗ monoListAuthOwn G.γep 1 eps)) }}

end spec

end EtcdGrove
end Perennial
