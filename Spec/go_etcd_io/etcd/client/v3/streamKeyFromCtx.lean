/-
`streamKeyFromCtx(ctx)` (`client/v3/watch.go:1102-1107`): the stream key of a context's outgoing
metadata (grpc's `metadata.FromOutgoingContext`, `fmt.Sprintf("%+v", ...)`).

Users: `watcher.Watch`, `watcher.RequestProgress` (the key that picks the shared stream),
`newWatcherGRPCStream` (`wgs.ctxKey`, which `closeStream` deletes). The key matters for the
principal: a watch that joins a stream another context opened is authenticated as that context's
principal, which `ctxStreamKey_prin` (`ApiWatch.lean`) equates with the caller's.

Proof sketch: `ctxPrin dflt ctx p`'s realization (W0) gives the context's outgoing metadata
(`Grpc.outMD ctx md`); `FromOutgoingContext.spec` (2a) gives a copy (`ok = false` only for
`md = []`); `fmt.Sprintf` of the map (`fmt`'s boundary, a function of the map's model) or `""`:
`ctxStreamKey ctx k` by its realization (`ApiWatch.lean`).

Changes: from `specs-ref`'s file of the same name: restated over this branch's vocabulary.
verify-round (A2-provability W2): the post was "some string", which let a watch joining a stream
another context opened have no fact relating its principal to the stream's; it now gives
`ctxStreamKey ctx k` (the old tree's `streamKeyOf`, whose laws are now `ctxStreamKey_prin`), and the
pre takes `ctxPrin` (every caller has it), whose realization carries the metadata.

Margin: mirrors the code (the key's text is not modelled; only what equal keys imply).
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

/-- `streamKeyFromCtx(ctx)`: the context's stream key (`ctxStreamKey`). -/
def streamKeyFromCtx.spec : Prop :=
  ∀ (ctx : GoInterface) (dflt p : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ Context.ctxOk ctx ∗
      ctxPrin dflt ctx p }}
    (App (Val (@! go_etcd_io.etcd.client.v3.streamKeyFromCtx)) (Val #ctx))
  {{ (k : GoString), RET #k; ctxStreamKey ctx k }}

end spec

end ClientV3
end EtcdGrove
end Perennial
