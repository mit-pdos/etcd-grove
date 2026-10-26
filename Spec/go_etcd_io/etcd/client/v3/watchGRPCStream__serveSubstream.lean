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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`w.serveSubstream(ws, resumec)`**, a lifetime `L` of the goroutine of the watch `P` (D25):
from any state of the substream (`wsRun`: its lifetime starting at `recvc`'s position `k0`, whose
first response is a created one, `lifeStart`, with half the request's `rev` field at `rv0`; the
buffer and both cursors as the previous lifetime left them), the fields it owns (`closing` `false`,
the buffer logger, `outc`, half of its lifetime's `donec`), the lifetime's invariant (`lifeSt`,
running: half its flag `L.γt`, half the membership token): receives `run`'s responses on `recvc`,
sends its channel on `retc` at the first created response ever (and publishes it if asked),
skips the later created ones (a resumed create), buffers the others and publishes them on `outc`
in order, each with the contract's facts, keeping the request's `rev` field the resume revision of
its responses (`resumeOk`); until `resumec` is closed (the generation `L.gen` ends: it leaves its
state in the lifetime's invariant, `resumeBody`), or `recvc` is closed or the stream's or the
watch's context is done (it stops for good: `closing` set for good, `γx` set, `stopBody` left in
the invariant, the membership token posted on `closingc`); it closes its `donec` (publishing
`lifeQ`) and signals the wait group, which gives it the thread token it exits with. -/
abbrev watchGRPCStream.serveSubstream.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (P : WsPrm GF) (L : LifePrm) (k0 : Nat)
    (rv0 : w64) (rcv : List Loc) (bl : Loc) (rc : Loc) (γrc : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isWGS V G callSl ∗
      wsIs V P ∗ wsRun V P k0 rv0 rcv rv0 ∗ ⌜rcv.length = k0⌝ ∗ lifeStart P k0 ∗
      wsF P.ws go!"closing" ↦ false ∗ wsF P.ws go!"bufLogger" ↦ bl ∗ bufLogOk P.ws bl ∗
      wsF P.ws go!"outc" ↦ P.outc ∗
      wsF P.ws go!"donec" ↦{DFrac.own (1 : Qp).half} L.dc ∗
      ownBroadcastChan L.dc L.γdn (lifeQ V G P L) .Pending ∗
      lifeInvIs V G P L ∗ dghostVar L.γt (DFrac.own (1 : Qp).half) false ∗
      ownBroadcastChan rc γrc (monoNatLbOwn G.γend (L.gen + 1)) .Unknown ∗
      dghostVar P.γx (DFrac.own 1) false ∗ wgDone G.wgs ∗
      ghostMapElem G.γws P.ws (DFrac.own (1 : Qp).half) () }}
    (App (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"serveSubstream")) (Val #P.ws)) (Val #rc))
  {{ RET #(); threadTok }}

end spec

end EtcdGrove
end Perennial
