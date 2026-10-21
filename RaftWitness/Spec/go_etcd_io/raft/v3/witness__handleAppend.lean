/-
`(*witness).handleAppend` (raft#168, `witness.go`; 2026-10-20, witness support).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `w.handleAppend(m, st)`: answered without a write as `handleAppendNoUpdate` against
`w.state`; else the state being built takes the request's entry and replication sets, and the
answer acknowledges its index at its term (`wAppend`). -/
abbrev witness.handleAppend.spec : Prop :=
  ∀ (w : Loc) (id : w64) (dq : DFrac) (p : Loc) (σ : WHS) (mv : WitnessMessage) (μ : WMsg)
    (q : Loc) (st : WHS),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ w.[witness, go!"id"] ↦□ id ∗
      w.[witness, go!"state"] ↦{dq} p ∗ whsOpt p σ ∗ ownWMsg mv μ ∗ whsOwn q st }}
    (App (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"handleAppend"))
      (Val #mv)) (Val #q))
  {{ (ml : Loc), RET #ml; w.[witness, go!"state"] ↦{dq} p ∗ whsOwn q (wAppend id σ st μ).1 ∗
      msgOwn ml (DFrac.own 1)
        ⟨(wAppend id σ st μ).2.1, [], none, (wAppend id σ st μ).2.2, []⟩ }}

end spec

end EtcdGrove
end Perennial
