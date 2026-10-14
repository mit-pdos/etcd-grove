/-
`copyKeyValue(kv, keysOnly)` (`client/v3/leasing/util.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`copyKeyValue(kv, keysOnly)`** of a cached key-value (read on any fraction): a fresh copy
(fresh key and value slices), the value dropped if `keysOnly`. -/
abbrev copyKeyValue.spec : Prop :=
  ∀ (c : CachedKv) (dq : DFrac) (keysOnly : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ cachedKvOwn c dq }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.copyKeyValue)) (Val #c.p)) (Val #keysOnly))
  {{ (p : Loc), RET #p; cachedKvOwn c dq ∗ ∃ c' : CachedKv,
      ⌜c'.p = p ∧ c'.kv = (if keysOnly then { c.kv with value := [] } else c.kv)⌝ ∗
      cachedKvOwn c' (DFrac.own 1) }}

end spec

end leasing
end EtcdGrove
end Perennial
