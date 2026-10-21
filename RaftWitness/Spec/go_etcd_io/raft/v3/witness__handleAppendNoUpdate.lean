/-
`(*witness).handleAppendNoUpdate` (raft#168, `witness.go`; 2026-10-20, witness support).
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

/-- `w.handleAppendNoUpdate(m)` against the witness's state `w.state` (`wAppendNoUpdate`): a
fresh `MsgAppResp` at the state's term, acknowledging the request's index (its entry has the
stored `(term, subterm)`) or the stored one (the request's is below it), and whether that
answers it (`false`: the state is to be written; the message's index is then `0`). -/
abbrev witness.handleAppendNoUpdate.spec : Prop :=
  ∀ (w : Loc) (id : w64) (dq : DFrac) (p : Loc) (σ : WHS) (mv : WitnessMessage) (μ : WMsg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ w.[witness, go!"id"] ↦□ id ∗
      w.[witness, go!"state"] ↦{dq} p ∗ whsOpt p σ ∗ ownWMsg mv μ }}
    (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"handleAppendNoUpdate"))
      (Val #mv))
  {{ (ml : Loc), RET (PairV #ml #(wAppendNoUpdate id σ μ).2); w.[witness, go!"state"] ↦{dq} p ∗
      msgOwn ml (DFrac.own 1)
        ⟨(wAppendNoUpdate id σ μ).1.1, [], none, (wAppendNoUpdate id σ μ).1.2, []⟩ }}

end spec

end EtcdGrove
end Perennial
