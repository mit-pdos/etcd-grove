/-
`etcdserverpb.ResponseHeader.GetRevision()` (`api/etcdserverpb/rpc.pb.go`, translated
for the store). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `h.GetRevision()`: the header's revision, `0` for a nil header (`hdrAt`). -/
abbrev ResponseHeader.GetRevision.spec : Prop :=
  ∀ (h : Loc) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ hdrAt h rev }}
    (App (Val (h @!! go.GoType.PointerType etcdserverpb.ResponseHeader.ty @!! go!"GetRevision")) (Val #()))
  {{ RET #rev; True }}

end spec

end EtcdGrove
end Perennial
