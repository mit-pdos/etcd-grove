/-
`Range` (`cache/predicate.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `Range(start, end)`: a closure implementing `rangePred start end` (`start <= k < end`, by
`bytes.Compare`). It keeps both slices, which must stay read-only. -/
abbrev Range.spec : Prop :=
  ∀ (startSl endSl : GoSlice) (start end_ : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      startSl ↦*□ start ∗ endSl ↦*□ end_ }}
    (App (App (Val (@! go_etcd_io.etcd.cache.v3.Range)) (Val #startSl)) (Val #endSl))
  {{ (f : GoFunc), RET #f; ⌜f ≠ func.nil⌝ ∗ keyPredSpec f (rangePred start end_) }}

end spec

end EtcdGrove
end Perennial
