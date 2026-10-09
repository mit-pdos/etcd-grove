/-
`clientv3.mustInt64orLeaseID(v)` (`client/v3/compare.go`, translated for `client/v3/concurrency`). Lean-first (no
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

/-- `mustInt64orLeaseID(v)` of a `LeaseID`, an `int64` or an `int` (anything else panics, which
the caller rules out): its value. -/
abbrev mustInt64orLeaseID.spec : Prop :=
  ∀ (v : GoInterface) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ⌜v = interface.mkOk go_etcd_io.etcd.client.v3.LeaseID.ty #n ∨ v = interface.mkOk go.int64 #n ∨
      v = interface.mkOk go.int #n⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.mustInt64orLeaseID)) (Val #v))
  {{ RET #n; True }}

end spec

end EtcdGrove
end Perennial
