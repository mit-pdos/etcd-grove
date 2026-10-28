/-
`(*urlPicker).unreachable` (`urlpick.go`; rafthttp stage 4). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Picker

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `p.unreachable(u)`: the next URL picked if `u` is the one picked. -/
abbrev rafthttp.urlPicker.unreachable.spec : Prop :=
  ∀ (pk : Loc) (P : net.url.URL → Prop) (u : net.url.URL),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      pickerOk pk P }}
    (App (Val (pk @!! go.GoType.PointerType rafthttp.urlPicker.ty @!! go!"unreachable")) (Val #u))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
