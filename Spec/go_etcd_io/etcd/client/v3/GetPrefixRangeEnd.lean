/-
`clientv3.GetPrefixRangeEnd(prefix)` (`client/v3/op.go`, translated for the cache).
Lean-first (no Rocq counterpart); see `InvCache.lean`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `GetPrefixRangeEnd(prefix)`: `prefixRangeEnd prefix`, the end of the range of keys with
prefix `prefix`. -/
abbrev GetPrefixRangeEnd.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.GetPrefixRangeEnd)) (Val #p))
  {{ RET #(prefixRangeEnd p); True }}

end spec

end EtcdGrove
end Perennial
