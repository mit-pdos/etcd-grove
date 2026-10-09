/-
`clientv3.IsOptsWithFromKey(opts)` (`client/v3/op.go`, translated for the cache). Lean-first (no Rocq
counterpart); see `InvOp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `IsOptsWithFromKey(opts)`: whether the options, applied to `NewOp()`, set `isOptsWithFromKey`. -/
abbrev IsOptsWithFromKey.spec : Prop :=
  ∀ (sl : GoSlice) (gs : List (OpFull → OpFull)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAt sl gs }}
    (App (Val (@! go_etcd_io.etcd.client.v3.IsOptsWithFromKey)) (Val #sl))
  {{ RET #((opFold gs OpFull.newOp).withFromKey); True }}

end spec

end EtcdGrove
end Perennial
