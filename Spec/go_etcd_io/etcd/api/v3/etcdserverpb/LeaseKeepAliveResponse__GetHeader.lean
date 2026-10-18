/-
`(*etcdserverpb.LeaseKeepAliveResponse).GetHeader()` (`api/etcdserverpb/rpc.pb.go`; item 1, the
client lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `x.GetHeader()` on a non-nil response whose `Header` field holds `h` (any fraction): `h`. -/
abbrev LeaseKeepAliveResponse.GetHeader.spec : Prop :=
  ∀ (x h : Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ⌜x ≠ null⌝ ∗ structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"Header" x ↦{dq} h }}
    (App (Val (x @!! go.GoType.PointerType etcdserverpb.LeaseKeepAliveResponse.ty @!! go!"GetHeader"))
      (Val #()))
  {{ RET #h; structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"Header" x ↦{dq} h }}

end spec

end EtcdGrove
end Perennial
