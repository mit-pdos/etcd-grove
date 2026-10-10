/-
`closeAll(chs)` (`client/v3/leasing/util.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`closeAll(chs)`**: closes each waiter channel (the caller's to close). -/
abbrev closeAll.spec : Prop :=
  ∀ (sl : GoSlice) (cs : List GoChan) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ sl ↦*{dq} cs ∗ ([∗list] c ∈ cs, waitcClose c) }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.closeAll)) (Val #sl))
  {{ RET #(); sl ↦*{dq} cs }}

end spec

end leasing
end EtcdGrove
end Perennial
