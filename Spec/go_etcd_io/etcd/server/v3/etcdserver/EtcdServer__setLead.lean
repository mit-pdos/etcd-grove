/-
`(*EtcdServer).setLead(v)` (server.go). Lean-first (no Rocq counterpart); the request path's unit
4c (2026-10-13: the ready handler's `updateLead`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.setLead(v)` stores `v` into the atomic `s.lead`. -/
abbrev EtcdServer.setLead.spec : Prop :=
  ∀ (s : Loc) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvLeadInv s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"setLead")) (Val #v))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
