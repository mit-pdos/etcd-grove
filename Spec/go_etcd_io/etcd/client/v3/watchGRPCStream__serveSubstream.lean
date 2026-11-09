/-
`(*watchGRPCStream).serveSubstream(ws, resumec)`: a substream's goroutine (forked by `run` and
`newWatchClient`, with a thread token deposited in `s.wg`, given back at `Done`).

**Proof sketch.** `ws.closing` is false (`⌜q.closing = false⌝`: the `panic` is unreachable). Loop:
deliver `buf`'s head on `outc` (its facts at the consumer's next position: `wsOwn`'s producer
half; an error response ends it), or a response from `recvc` (with its `watchStep` facts at the
substream's position: `run` established them, `deliverOk`): a first `Created` hands `outc` to
`Watch` on `retc` (and to the consumer if `createdNotify`), and for `rev = 0` sets the resume
revision to the header's (the position stays unknown: `WatchPos.init 0`'s `none`, see
`ApiWatch.lean`); a progress raises `initReq.rev` (never lowers it: the fork's fix); events set it
past the last; `recvc` closed, `ctx.Done()`, `ws.initReq.ctx.Done()`: stop (closing, `closingc`);
`resumec`: stop for a resume (`wsOwn` back to `run` at `donec`).

Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
**Margin**: mirrors the code.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WatchInternal

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

/-- `s.serveSubstream(ws, resumec)`: never panics; ends with a thread token (`wg.Done`). -/
def watchGRPCStream.serveSubstream.spec : Prop :=
  ∀ (s w ws : Loc) (γ : Cluster) (who : Principal) (wq : WatchReq) (q : WsM) (resumec : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsAt s w γ who ∗ wsAt ws s γ who wq ∗ wsOwn ws s γ who q ∗
      wsServe ws s γ who resumec ∗ ⌜q.closing = false⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"serveSubstream")) (Val #ws)) (Val #resumec))
  {{ RET #(); threadTok }}

end spec

end ClientV3
end EtcdGrove
end Perennial
