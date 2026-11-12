/-
`store.applyEventsLocked` (`cache/*.go`), an internal helper.
Users: `store.Apply`.
Proof sketch: for each revision's events: deletes (`BTree.Delete.spec`; the key present, so no error) and puts (`newKVItem.spec`, `BTree.ReplaceOrInsert.spec`), then the revision's snapshot (`newClonedSnapshot.spec`, `ringBuffer.Append.spec`) certified by the events (`deliv`), `revCond` broadcast.
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

/-- `s.applyEventsLocked(events)` under the lock, for events certified from `a`, above the latest revision. -/
def store.applyEventsLocked.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (pfx : GoString) (lr : Nat) (a b : Int) (evSl : GoSlice)
    (evs : List RevEvent) (σ : State) (r : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ storeLocked s γ pfx lr ∗ eventsAt evSl evs ∗ etcdLb γ σ ∗ storeUpTo s a ∗ storeCeilLb s r ∗ ⌜deliv σ.kv (prefixRange pfx) (some a) evs b ∧ ∀ e ∈ evs, lr < e.rev ∧ e.rev ≤ r⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.store.ty @!! go!"applyEventsLocked")) (Val #evSl))
  {{ RET #GoInterface.nil; ∃ lr', storeLocked s γ pfx lr' ∗ ⌜evs.getLast?.map (·.rev) = some lr'⌝ }}

end spec

end Cache
end EtcdGrove
end Perennial
