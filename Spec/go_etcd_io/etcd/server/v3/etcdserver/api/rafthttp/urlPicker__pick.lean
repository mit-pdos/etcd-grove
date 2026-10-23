/-
`(*urlPicker).pick` (`urlpick.go`; rafthttp stage 4). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Picker

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `p.pick()`: one of the URLs. -/
abbrev rafthttp.urlPicker.pick.spec : Prop :=
  ∀ (pk : Loc) (P : net.url.URL → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      pickerOk pk P }}
    (App (Val (pk @!! go.GoType.PointerType rafthttp.urlPicker.ty @!! go!"pick")) (Val #()))
  {{ (u : net.url.URL), RET #u; ⌜P u⌝ }}

end spec

end EtcdGrove
end Perennial
