/-
`etcdserverpb.ResponseHeader.GetLeaderId()` (`api/etcdserverpb/rpc.pb.go`, translated for
`client/v3/leasing`'s `copyHeader`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

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
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `h.GetLeaderId()`: the field `LeaderId` of a non-nil header (read-only). -/
abbrev ResponseHeader.GetLeaderId.spec : Prop :=
  ∀ (h : Loc) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"LeaderId" h ↦□ v }}
    (App (Val (h @!! go.GoType.PointerType etcdserverpb.ResponseHeader.ty @!! go!"GetLeaderId")) (Val #()))
  {{ RET #v; True }}

end spec

end EtcdGrove
end Perennial
