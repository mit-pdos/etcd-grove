/-
`store.applyProgressNotifyLocked` (`cache/*.go`), an internal helper.
Users: `store.Apply`.
Proof sketch: sets `latest.rev` (if restored) and broadcasts on `revCond`; the newest snapshot's gap extended by the quiet fact.
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

/-- `s.applyProgressNotifyLocked(rev)` under the lock, for a quiet notification at `rev ≥` the latest. -/
def store.applyProgressNotifyLocked.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (pfx : GoString) (lr : Nat) (a : Int) (rev : w64) (σ : State) (r : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ storeLocked s γ pfx lr ∗ etcdLb γ σ ∗ storeUpTo s a ∗ storeCeilLb s r ∗ ⌜lr ≤ sint.Z rev ∧ sint.Z rev ≤ r ∧ 0 < sint.Z rev ∧ quiet σ.kv (prefixRange pfx) (some a) (sint.Z rev).toNat⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.store.ty @!! go!"applyProgressNotifyLocked")) (Val #rev))
  {{ RET #(); storeLocked s γ pfx (if lr = 0 then 0 else (sint.Z rev).toNat) }}

end spec

end Cache
end EtcdGrove
end Perennial
