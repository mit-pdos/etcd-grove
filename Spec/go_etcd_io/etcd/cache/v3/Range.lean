/-
`Range` (`cache/*.go`).
Users: `KeyPredForRange`.
Proof sketch: two `bytes.Compare`s against the captured slices.
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

/-- `Range(start, end)`: a predicate deciding `start ≤ k < end`. -/
def Range.spec : Prop :=
  ∀ (startSl endSl : GoSlice) (start end_ : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ startSl ↦*□ start ∗ endSl ↦*□ end_ }}
    (App (App (Val (@! go_etcd_io.etcd.cache.v3.Range)) (Val #startSl)) (Val #endSl))
  {{ (f : GoFunc), RET #f; keyPredAt f (fun k => EtcdModel.keyLe start k ∧ EtcdModel.keyLt k end_) }}

end spec

end Cache
end EtcdGrove
end Perennial
