/-
`(*watchGRPCStream).backoffIfUnavailable(backoff, err)`: on an `Unavailable` error (1c's `isUnavailableErr`), sleeps a growing backoff (at most `maxBackoff`). Users: `run`, `openWatchClient`.
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

/-- `s.backoffIfUnavailable(backoff, err)`: the next backoff. -/
def watchGRPCStream.backoffIfUnavailable.spec : Prop :=
  ∀ (s w : Loc) (γ : Cluster) (who : Principal) (backoff : w64) (err : GoInterface) (k : CallErr),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsAt s w γ who ∗ callErr err k }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"backoffIfUnavailable")) (Val #backoff)) (Val #err))
  {{ (b : w64), RET #b; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
