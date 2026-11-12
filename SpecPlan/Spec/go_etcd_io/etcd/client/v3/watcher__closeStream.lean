/-
`(*watcher).closeStream(wgs)`: `run`'s teardown: under `mu`, close `donec` (once: `wgsDoneTok`, publishing `closeErr`), cancel, drop the map entry. Users: `run`'s deferred function.
Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
verify-round (W3): `watcherHandle` records its client `c`.
**Margin**: mirrors the code.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.WatchInternal

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

/-- `w.closeStream(s)`: `s` closed and forgotten. -/
def watcher.closeStream.spec : Prop :=
  ∀ (w c s : Loc) (γ : Cluster) (who p : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ watcherHandle w c γ who ∗ wgsAt s w γ p ∗ wgsDoneTok s γ p }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"closeStream")) (Val #s))
  {{ RET #(); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
