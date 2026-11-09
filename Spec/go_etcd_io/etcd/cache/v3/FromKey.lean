/-
`FromKey` (`cache/*.go`).
Users: `KeyPredForRange`.
Proof sketch: `bytes.Compare` against the captured slice.
Changes: restated over `keyPredAt`; unchanged.
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

/-- `FromKey(start)`: a predicate deciding `start ≤ k`. -/
def FromKey.spec : Prop :=
  ∀ (sl : GoSlice) (start : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ sl ↦*□ start }}
    (App (Val (@! go_etcd_io.etcd.cache.v3.FromKey)) (Val #sl))
  {{ (f : GoFunc), RET #f; keyPredAt f (fun k => EtcdModel.keyLe start k) }}

end spec

end Cache
end EtcdGrove
end Perennial
