/-
`Cache.serverRevision` (`cache/*.go`), an internal helper.
Users: `Cache.Get` (a linearizable read's target).
Proof sketch: the client's `Get` (`isCache`'s `kvAt`, `KV.GetTriple` at the call's principal `p` with `ctxPrin who ctx p`, `lo = 0` and `authLb γ 0` by its left disjunct) of one key, count-only, with the persistent update built from `etcdPeek γ` (a range leaves the state, `kvStep`), whose `Q` records `etcdLb γ σ1` at the firing and `σ0`'s order (`etcdLb_reach` inside it); a linearizable range answers at `σ1.kv.rev` (`kvStep`); the header's revision.
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

/-- `c.serverRevision(ctx)`: the revision of a state the cluster was in during the call (after `σ0`), or an error. -/
def Cache.serverRevision.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who p : Principal) (pfx : GoString) (ctx : GoInterface) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ etcdLb γ σ0 }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"serverRevision")) (Val #ctx))
  {{ (r : w64) (err : GoInterface), RET (PairV #r #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ1 : State, etcdLb γ σ1 ∗ ⌜sint.Z r = σ1.kv.rev ∧ σ0.kv.rev ≤ σ1.kv.rev⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end Cache
end EtcdGrove
end Perennial
