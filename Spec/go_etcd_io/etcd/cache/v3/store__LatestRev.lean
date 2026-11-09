/-
`store.LatestRev` (`cache/*.go`), an internal helper.
Users: `Cache.Get`, `Cache.WaitForRevision`, `Cache.waitTillRevision`.
Proof sketch: reads `latest.rev` under the read lock; the invariant's `storeRevLb` authority and the cluster's lower bound.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

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

/-- `s.LatestRev()`: a revision the store reached, which the cluster reached. -/
def store.LatestRev.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isStore s γ pfx ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.store.ty @!! go!"LatestRev")) (Val #()))
  {{ (r : w64), RET #r; threadTok ∗ ⌜0 ≤ sint.Z r⌝ ∗ storeRevLb s (sint.Z r).toNat ∗
      ∃ σ : State, etcdLb γ σ ∗ ⌜sint.Z r ≤ σ.kv.rev⌝ }}

end spec

end Cache
end EtcdGrove
end Perennial
