/-
`clientv3.WithIgnoreLease()` (`client/v3/op.go`, translated for `client/v3/leasing`); see `InvOp.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `WithIgnoreLease()`: an option setting `ignoreLease`. -/
abbrev WithIgnoreLease.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithIgnoreLease)) (Val #()))
  {{ (f : GoFunc), RET #f; optSpec f withIgnoreLeaseM }}

end spec

end EtcdGrove
end Perennial
