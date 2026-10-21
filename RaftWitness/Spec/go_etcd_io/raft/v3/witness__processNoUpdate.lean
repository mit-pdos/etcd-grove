/-
`(*witness).processNoUpdate` (raft#168, `witness.go`; 2026-10-20, witness support).
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

/-- `w.processNoUpdate(m)` against the cache `w.state` (`wNoUpdate`): handled without the
storage (a heartbeat while unhealthy: no answer; an older term: `processMessageWithOlderTerm`'s;
an append of the cache's term that `handleAppendNoUpdate` answers), with its answer; or not
(`false`). -/
abbrev witness.processNoUpdate.spec : Prop :=
  ∀ (w : Loc) (id : w64) (cq pv : Bool) (dq dq' : DFrac) (p : Loc) (σ : WHS) (e : GoError)
    (mv : WitnessMessage) (μ : WMsg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ w.[witness, go!"id"] ↦□ id ∗
      w.[witness, go!"checkQuorum"] ↦□ cq ∗ w.[witness, go!"preVote"] ↦□ pv ∗
      w.[witness, go!"state"] ↦{dq} p ∗ whsOpt p σ ∗ w.[witness, go!"lastError"] ↦{dq'} e ∗
      ownWMsg mv μ }}
    (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"processNoUpdate")) (Val #mv))
  {{ (ml : Loc) (h : Bool), RET (PairV #ml #h); w.[witness, go!"state"] ↦{dq} p ∗
      w.[witness, go!"lastError"] ↦{dq'} e ∗
      match wNoUpdate id cq pv (decide (e = interface.nil)) σ μ with
      | some r => ⌜h = true⌝ ∗ respOpt ml r
      | none => ⌜h = false⌝ }}

end spec

end EtcdGrove
end Perennial
