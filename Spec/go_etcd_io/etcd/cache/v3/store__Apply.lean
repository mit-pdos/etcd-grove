/-
`store.Apply` (`cache/*.go`), an internal helper.
Users: `Cache.applyStorage` (each store watcher response).
Proof sketch: a canceled response errs; under the write lock `validateRevisions.spec` (a stale response errs: an old applier's, after a re-list); a progress notification (`applyProgressNotifyLocked.spec`) or events (`applyEventsLocked.spec`): certified from `a`, every prefix event below `a` already in the store (`storeUpTo`), so the new snapshots and gaps are certified.
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

/-- `s.Apply(resp)` for a store watcher's response certified from `a` (within the ceiling): `nil` and the store covers up to the response's next position, or an error. -/
def store.Apply.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (pfx : GoString) (a : Int) (pos' : Option Int) (r : Nat)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isStore s γ pfx ∗ watchRespAt resp m ∗ respFact γ (prefixRange pfx) (some a) m pos' ∗ storeUpTo s a ∗ storeCeilLb s r ∗ ⌜m.hdrRev ≤ r ∧ ∀ e ∈ m.events, e.rev ≤ r⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.store.ty @!! go!"Apply")) (Val #resp))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∀ b, ⌜pos' = some b⌝ -∗ storeUpTo s b) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end Cache
end EtcdGrove
end Perennial
