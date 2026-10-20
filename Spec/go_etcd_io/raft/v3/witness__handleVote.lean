/-
`(*witness).handleVote` (raft#168, `witness.go`; 2026-10-20, witness support).
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

/-- `w.handleVote(m, st)` on the state being built (`wVote`): the grant or rejection, the vote
recorded on a grant (not a pre-vote's). -/
abbrev witness.handleVote.spec : Prop :=
  ∀ (w : Loc) (id : w64) (mv : WitnessMessage) (μ : WMsg) (q : Loc) (st : WHS),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ w.[witness, go!"id"] ↦□ id ∗
      ownWMsg mv μ ∗ whsOwn q st }}
    (App (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"handleVote"))
      (Val #mv)) (Val #q))
  {{ (ml : Loc), RET #ml; whsOwn q (wVote id st μ).1 ∗
      msgOwn ml (DFrac.own 1) ⟨(wVote id st μ).2.1, [], none, (wVote id st μ).2.2, []⟩ }}

end spec

end EtcdGrove
end Perennial
