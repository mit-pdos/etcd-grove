/-
`demux.broadcastLocked` (`cache/*.go`), an internal helper.
Users: `demux.Broadcast`.
Proof sketch: dispatches to `broadcastProgressLocked` or `broadcastEventsLocked` (or nothing).
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `d.broadcastLocked(resp)`: the pending response broadcast. -/
def demux.broadcastLocked.spec : Prop :=
  ∀ (d : Loc) (γ : Cluster) (pfx : GoString) (s : Loc)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ demuxLocked d γ pfx s (some m) ∗ watchRespAt resp m }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.demux.ty @!! go!"broadcastLocked")) (Val #resp))
  {{ RET #(); demuxLocked d γ pfx s none }}

end spec

end Cache
end EtcdGrove
end Perennial
