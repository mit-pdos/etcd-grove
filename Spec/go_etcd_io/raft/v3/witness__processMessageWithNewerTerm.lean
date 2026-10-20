/-
`(*witness).processMessageWithNewerTerm` (raft#168, `witness.go`; 2026-10-20, witness support).
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

/-- `w.processMessageWithNewerTerm(m, st)`, for a request of a newer term: the state being built
moves to it (`wNewer`: a pre-vote changes nothing; the vote is cleared, the leader is the
sender of a leader's message, none for others). -/
abbrev witness.processMessageWithNewerTerm.spec : Prop :=
  ∀ (w : Loc) (mv : WitnessMessage) (μ : WMsg) (q : Loc) (st : WHS),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownWMsg mv μ ∗ whsOwn q st }}
    (App (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"processMessageWithNewerTerm"))
      (Val #mv)) (Val #q))
  {{ RET #(); whsOwn q (wNewer st μ) }}

end spec

end EtcdGrove
end Perennial
