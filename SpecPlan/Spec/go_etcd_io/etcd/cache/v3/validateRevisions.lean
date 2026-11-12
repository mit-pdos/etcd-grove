/-
`validateRevisions` (`cache/*.go`), an internal helper.
Users: `demux.Broadcast`, `store.Apply`.
Proof sketch: pure: the progress notification's revision against `latestRev`, or each event's.
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

/-- `validateRevisions(resp, latestRev)`: `nil` iff a progress notification is not below `latestRev`, or every event is above it. -/
def validateRevisions.spec : Prop :=
  ∀ (resp : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM) (latestRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ watchRespAt resp m }}
    (App (App (Val (@! go_etcd_io.etcd.cache.v3.validateRevisions)) (Val #resp)) (Val #latestRev))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil ↔
        (if m.events = [] ∧ m.canceled = false ∧ m.created = false ∧ m.compactRev = 0 ∧ m.hdrRev ≠ 0
         then sint.Z latestRev ≤ m.hdrRev else ∀ e ∈ m.events, sint.Z latestRev < e.rev)⌝ }}

end spec

end Cache
end EtcdGrove
end Perennial
