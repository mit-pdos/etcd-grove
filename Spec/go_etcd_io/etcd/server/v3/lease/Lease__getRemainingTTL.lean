/-
`(*Lease).getRemainingTTL` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); see
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

/-- `l.getRemainingTTL()`: the checkpointed `remainingTTL` if positive, else `ttl`. -/
abbrev lease.Lease.getRemainingTTL.spec : Prop :=
  ∀ (l : Loc) (r t : w64) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lsF go!"remainingTTL" l ↦{dq1} r ∗ lsF go!"ttl" l ↦{dq2} t }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"getRemainingTTL")) (Val #()))
  {{ RET #(if 0 < sint.Z r then r else t);
      lsF go!"remainingTTL" l ↦{dq1} r ∗ lsF go!"ttl" l ↦{dq2} t }}

end spec

end EtcdGrove
end Perennial
