/-
`streamKeyFromCtx(ctx)`: the stream key of a context's outgoing metadata (grpc's `metadata.FromOutgoingContext`, `fmt.Sprintf`). Users: `Watch`, `RequestProgress`. No client statement depends on which stream a watch joins (`nonissues/etcd-watch-stream-key-collision.md`: harmless here, every stream carries the client's principal).
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

/-- `streamKeyFromCtx(ctx)`: some string. -/
def streamKeyFromCtx.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ Context.ctxOk ctx }}
    (App (Val (@! go_etcd_io.etcd.client.v3.streamKeyFromCtx)) (Val #ctx))
  {{ (k : GoString), RET #k; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
