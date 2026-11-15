/-
`ExactKey` (`cache/*.go`).
Users: `KeyPredForRange` (the watchers' filters).
Proof sketch: returns a closure over `key` calling `bytes.Equal` (Perennial's `bytes` spec), reading the captured slice read-only.
Changes: restated over `keyPredAt`; unchanged.
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Api

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

/-- `ExactKey(key)`: a predicate deciding `k = key`. -/
def ExactKey.spec : Prop :=
  ∀ (sl : GoSlice) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ sl ↦*□ key }}
    (App (Val (@! go_etcd_io.etcd.cache.v3.ExactKey)) (Val #sl))
  {{ (f : GoFunc), RET #f; keyPredAt f (fun k => k = key) }}

end spec

end Cache
end EtcdGrove
end Perennial
