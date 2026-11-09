/-
`Cache.validateWatch` (`cache/*.go`), an internal helper.
Users: `Cache.Watch`.
Proof sketch: the `Op`'s flags (`opAt`, W0's getters), a wrapped `ErrUnsupportedRequest` (`fmt.Errorf`); `Cache.validateRange.spec`; `KeyPredForRange.spec`.
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

/-- `c.validateWatch(key, op)`: the range's predicate, or a non-`nil` error (`ErrKeyRangeInvalid` for a served request whose range the cache does not serve). -/
def Cache.validateWatch.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (key : GoString)
    (op : go_etcd_io.etcd.client.v3.Op) (o : OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ opAt op o }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"validateWatch")) (Val #key)) (Val #op))
  {{ (f : GoFunc) (err : GoInterface), RET (PairV #f #err);
      (⌜¬ watchUnsupported o ∧ rangeOk pfx (cacheRange key o) ∧ err = GoInterface.nil⌝ ∗
        keyPredAt f (KeyRange.mem (cacheRange key o))) ∨
      (⌜watchUnsupported o ∧ err ≠ GoInterface.nil⌝) ∨
      (⌜¬ watchUnsupported o ∧ ¬ rangeOk pfx (cacheRange key o)⌝ ∗
        globalAddr go_etcd_io.etcd.cache.v3.ErrKeyRangeInvalid ↦□ err) }}

end spec

end Cache
end EtcdGrove
end Perennial
