/-
`(*Lease).TTL` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `l.TTL()`: its `ttl`. -/
abbrev lease.Lease.TTL.spec : Prop :=
  ∀ (l : Loc) (t : w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lsF go!"ttl" l ↦{dq} t }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"TTL")) (Val #()))
  {{ RET #t; lsF go!"ttl" l ↦{dq} t }}

end spec

end EtcdGrove
end Perennial
