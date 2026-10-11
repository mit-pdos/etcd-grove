/-
`probeItemFromKey(key)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `probeItemFromKey(key)`: a new read-only `kvItem` with key `string(key)` and no
`KeyValue`, to search the btree with. -/
abbrev probeItemFromKey.spec : Prop :=
  ∀ (sl : GoSlice) (key : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ sl ↦*{dq} key }}
    (App (Val (@! probeItemFromKey)) (Val #sl))
  {{ (p : Loc), RET #p; sl ↦*{dq} key ∗ kvItemIs p (key, null) }}

end spec

end EtcdGrove
end Perennial
