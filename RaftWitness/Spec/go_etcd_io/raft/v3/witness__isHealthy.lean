/-
`(*witness).isHealthy` (raft#168, `witness.go`; 2026-10-20, witness support).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `w.isHealthy()`: the last storage access did not fail. -/
abbrev witness.isHealthy.spec : Prop :=
  ∀ (w : Loc) (dq : DFrac) (e : GoError),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ w.[witness, go!"lastError"] ↦{dq} e }}
    (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"isHealthy")) (Val #()))
  {{ RET #(decide (e = interface.nil)); w.[witness, go!"lastError"] ↦{dq} e }}

end spec

end EtcdGrove
end Perennial
