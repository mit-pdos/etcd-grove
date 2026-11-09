/-
`KeyPredForRange` (`cache/*.go`).
Users: `Cache.validateGet`, `Cache.validateWatch` (the watcher's filter).
Proof sketch: a case split on `end`'s length and first byte; `ExactKey.spec`, `FromKey.spec` or `Range.spec`.
Changes: restated over `keyPredAt` and W0's `KeyRange.mem` (the old `keyPredForRange`); unchanged.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Api

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

/-- `KeyPredForRange(start, end)`: a predicate deciding membership in the range `{start, end}` (W0's `KeyRange.mem`). -/
def KeyPredForRange.spec : Prop :=
  ∀ (startSl endSl : GoSlice) (start end_ : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ startSl ↦*□ start ∗ endSl ↦*□ end_ }}
    (App (App (Val (@! go_etcd_io.etcd.cache.v3.KeyPredForRange)) (Val #startSl)) (Val #endSl))
  {{ (f : GoFunc), RET #f; keyPredAt f (fun k => KeyRange.mem { key := start, rangeEnd := end_ } k) }}

end spec

end Cache
end EtcdGrove
end Perennial
