/-
`ExactKey` (`cache/predicate.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
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

/-- `ExactKey(key)`: a closure implementing `exactKeyPred key` (`bytes.Equal(k, key)`). It
keeps `key`, so `key`'s slice must stay read-only. -/
abbrev ExactKey.spec : Prop :=
  ∀ (sl : GoSlice) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ sl ↦*□ key }}
    (App (Val (@! go_etcd_io.etcd.cache.v3.ExactKey)) (Val #sl))
  {{ (f : GoFunc), RET #f; ⌜f ≠ func.nil⌝ ∗ keyPredSpec f (exactKeyPred key) }}

end spec

end EtcdGrove
end Perennial
