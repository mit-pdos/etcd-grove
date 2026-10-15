/-
`s.StoppingNotify()` (`server.go`). Lean-first (no Rocq counterpart); the watch slice's unit W-W
(2026-10-15): the stop channel the stream interceptor's leader monitor (`monitorLeader`) selects
on. The same getter as `Stopping()`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.StoppingNotify()`: the `stopping` field. -/
abbrev EtcdServer.StoppingNotify.spec : Prop :=
  ∀ (s ch : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvStoppingAddr s ↦□ ch }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"StoppingNotify")) (Val #()))
  {{ RET #ch; True }}

end spec

end EtcdGrove
end Perennial
