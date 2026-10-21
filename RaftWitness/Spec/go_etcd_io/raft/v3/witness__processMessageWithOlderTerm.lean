/-
`(*witness).processMessageWithOlderTerm` (raft#168, `witness.go`; 2026-10-20, witness support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvWitness

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

/-- `w.processMessageWithOlderTerm(m)`, for a request of a term older than `w.state`'s: the answer
`wOlder` (a `MsgAppResp` at the newer term to a stale leader under check-quorum or pre-vote, a
pre-vote's rejection, or none). Stated on the fields it reads. -/
abbrev witness.processMessageWithOlderTerm.spec : Prop :=
  ∀ (w : Loc) (id : w64) (cq pv : Bool) (dq : DFrac) (p : Loc) (σ : WHS) (mv : WitnessMessage)
    (μ : WMsg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ w.[witness, go!"id"] ↦□ id ∗
      w.[witness, go!"checkQuorum"] ↦□ cq ∗ w.[witness, go!"preVote"] ↦□ pv ∗
      w.[witness, go!"state"] ↦{dq} p ∗ whsOpt p σ ∗ ownWMsg mv μ }}
    (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"processMessageWithOlderTerm"))
      (Val #mv))
  {{ (ml : Loc), RET #ml; w.[witness, go!"state"] ↦{dq} p ∗ respOpt ml (wOlder id cq pv σ μ) }}

end spec

end EtcdGrove
end Perennial
