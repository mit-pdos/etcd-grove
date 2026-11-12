/-
`demux.LatestRev` (`cache/*.go`), an internal helper.
Users: none in the cache (kept: verified before).
Proof sketch: reads `maxRev` under the read lock; the invariant holds it reached by the cluster.
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

/-- `d.LatestRev()`: a revision the cluster reached. -/
def demux.LatestRev.spec : Prop :=
  ∀ (d : Loc) (γ : Cluster) (pfx : GoString) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γ pfx s ∗ threadTok }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.demux.ty @!! go!"LatestRev")) (Val #()))
  {{ (r : w64), RET #r; threadTok ∗ ∃ σ : State, etcdLb γ σ ∗ ⌜sint.Z r ≤ σ.kv.rev⌝ }}

end spec

end Cache
end EtcdGrove
end Perennial
