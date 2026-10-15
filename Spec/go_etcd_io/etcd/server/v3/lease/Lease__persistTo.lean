/-
`(*Lease).persistTo` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/LessorBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `l.persistTo(b)`: writes the lease's record (`ID`, `ttl`, `remainingTTL`, read) into the
backend's `Lease` bucket under the batch lock, the critical-section contract's `Pre` to `Post`. -/
abbrev lease.Lease.persistTo.spec : Prop :=
  ∀ (l : Loc) (b : GoInterface) (P : IProp GF) (f : val) (Pre Q Post : IProp GF)
    (id t r : w64) (dq1 dq2 dq3 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ leaseBackend b P f ∗
      mvcc.csContract P f Pre Q Post ∗
      lsF go!"ID" l ↦{dq1} id ∗ lsF go!"ttl" l ↦{dq2} t ∗ lsF go!"remainingTTL" l ↦{dq3} r }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"persistTo")) (Val #b))
  {{ RET #(); Post ∗
      lsF go!"ID" l ↦{dq1} id ∗ lsF go!"ttl" l ↦{dq2} t ∗ lsF go!"remainingTTL" l ↦{dq3} r }}

end spec

end EtcdGrove
end Perennial
