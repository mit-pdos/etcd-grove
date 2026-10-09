/-
`clientv3.getPrefix(key)` (`client/v3/op.go`, translated for the cache). Lean-first (no
Rocq counterpart); see `InvCache.lean`.
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

/-- `getPrefix(key)`: a read-only byte slice holding `prefixRangeEnd key` (a fresh copy of
`key`, incremented and truncated, or the package's `noPrefixEnd`, shared, hence read-only
for every caller). -/
abbrev getPrefix.spec : Prop :=
  ∀ (sl : GoSlice) (key : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ sl ↦*{dq} key }}
    (App (Val (@! go_etcd_io.etcd.client.v3.getPrefix)) (Val #sl))
  {{ (out : GoSlice), RET #out; sl ↦*{dq} key ∗ out ↦*□ prefixRangeEnd key }}

end spec

end EtcdGrove
end Perennial
