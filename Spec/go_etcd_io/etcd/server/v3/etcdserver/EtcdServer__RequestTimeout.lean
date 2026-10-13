/-
`s.RequestTimeout()` (`interface.go`). Lean-first (no Rocq counterpart); the request path's unit 4b
(2026-10-13): a method of the read loop's `server` interface (`read/Inv.lean`, `isReadServer`).
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

/-- `s.RequestTimeout()`: `s.Cfg.ReqTimeout()`, some duration. -/
abbrev EtcdServer.RequestTimeout.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜structFieldRef EtcdServer go!"Cfg" s ≠ null⌝ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"RequestTimeout")) (Val #()))
  {{ (d : _root_.Perennial.time.Duration), RET #d; True }}

end spec

end EtcdGrove
end Perennial
