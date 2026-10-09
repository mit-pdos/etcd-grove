/-
`clientv3.Version(key)` (`client/v3/compare.go`, translated for `client/v3/concurrency`). Lean-first (no
Rocq counterpart); see `InvCmp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvCmp

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

/-- `Version(key)`: a fresh comparison of the key's version, `&pb.Compare{Key: []byte(key), Target: ...}`
(operator `EQUAL`, no operand). -/
abbrev Version.spec : Prop :=
  ∀ (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.Version)) (Val #key))
  {{ (c : go_etcd_io.etcd.client.v3.Cmp), RET #c; cmpAt c (cmpKeyM .version key) }}

end spec

end EtcdGrove
end Perennial
