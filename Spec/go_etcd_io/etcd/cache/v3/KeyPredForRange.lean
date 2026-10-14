/-
`KeyPredForRange` (`cache/predicate.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `KeyPredForRange(start, end)`: a closure implementing `keyPredForRange start end`, the
key filter of `snapshot.Range`'s `kvRange` (`mem_kvRange`). The slices must stay read-only. -/
abbrev KeyPredForRange.spec : Prop :=
  ∀ (startSl endSl : GoSlice) (start end_ : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      startSl ↦*□ start ∗ endSl ↦*□ end_ }}
    (App (App (Val (@! go_etcd_io.etcd.cache.v3.KeyPredForRange)) (Val #startSl)) (Val #endSl))
  {{ (f : GoFunc), RET #f; ⌜f ≠ func.nil⌝ ∗ keyPredSpec f (keyPredForRange start end_) }}

end spec

end EtcdGrove
end Perennial
