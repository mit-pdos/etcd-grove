/-
`Cache.validateRange` (`cache/*.go`), an internal helper.
Users: `Cache.validateGet`, `Cache.validateWatch`.
Proof sketch: `GetPrefixRangeEnd` (W0's spec, `prefixEnd`), `bytes.Compare`s; `ErrKeyRangeInvalid`'s value (`init.spec`).
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

/-- `c.validateRange(start, end)`: `nil` iff the cache serves the range (`rangeOk`), else `ErrKeyRangeInvalid`. -/
def Cache.validateRange.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (startSl endSl : GoSlice) (sk ek : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ startSl ↦*□ sk ∗ endSl ↦*□ ek }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"validateRange")) (Val #startSl)) (Val #endSl))
  {{ (err : GoInterface), RET #err;
      (⌜rangeOk pfx ({ key := sk, rangeEnd := ek } : KeyRange) ∧ err = GoInterface.nil⌝) ∨
      (⌜¬ rangeOk pfx ({ key := sk, rangeEnd := ek } : KeyRange)⌝ ∗ globalAddr go_etcd_io.etcd.cache.v3.ErrKeyRangeInvalid ↦□ err) }}

end spec

end Cache
end EtcdGrove
end Perennial
