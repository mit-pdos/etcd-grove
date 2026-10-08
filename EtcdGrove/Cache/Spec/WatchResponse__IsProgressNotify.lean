/-
`clientv3.WatchResponse.IsProgressNotify()` (`client/v3/watch.go`, translated
for the store). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
import EtcdGrove.Cache.InvStore

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `wr.IsProgressNotify()`: `RespModel.isProgressNotify` (no events, not canceled, not
created, no compact revision, a non-zero header revision). A read, on any fraction. -/
abbrev WatchResponse.IsProgressNotify.spec : Prop :=
  ∀ (wr : Loc) (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wr ↦{dq} resp ∗ respAt resp r }}
    (App (Val (wr @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.WatchResponse.ty @!! go!"IsProgressNotify")) (Val #()))
  {{ RET #(r.isProgressNotify); wr ↦{dq} resp }}

end spec

end EtcdGrove
end Perennial
