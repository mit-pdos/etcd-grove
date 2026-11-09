/-
`Cache.get` (`cache/*.go`), an internal helper.
Users: `Cache.getWatch`.
Proof sketch: the client's `Get` of the prefix (`WithPrefix`, linearizable) with the update from `etcdPeek γ`, recording `etcdLb γ σ` at the firing and the ceiling's revision below it (the loop's lower bound, `etcdLb_reach`); on success `store.Restore.spec` (the answer is `σ.kv.store` in the prefix range: `kvStep`, `RangeReq.answers` with no limit, sort or filter) under the ceiling (`storeCeil`, in `cacheLoop`).
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

/-- `c.get(ctx)` by the watch loop: the list's response (read-only: the store keeps its key-values) and the loop restored at its revision, or an error. -/
def Cache.get.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ cacheLoop c ∗ Context.ctxOk ctx ∗ ctxPrin ctx who }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"get")) (Val #ctx))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ cacheLoop c) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (r : Nat) (m : RangeRespM), rangeRespOwn resp DFrac.discard m ∗
        ⌜m.hdr.map (·.revision) = some (W64 r)⌝ ∗ cacheLoopAt c r) }}

end spec

end Cache
end EtcdGrove
end Perennial
