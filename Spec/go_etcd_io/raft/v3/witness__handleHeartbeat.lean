/-
`(*witness).handleHeartbeat` (raft#168, `witness.go`; 2026-10-20, witness support).
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

/-- `w.handleHeartbeat(m, term)`: a fresh `MsgHeartbeatResp` to the request's sender carrying its
context, at the witness's term `term` (`wHeartbeat`; the caller's, fork `9ed005d46`). Stated on
the field it reads, `w.id`. -/
abbrev witness.handleHeartbeat.spec : Prop :=
  ∀ (w : Loc) (id : w64) (mv : WitnessMessage) (μ : WMsg) (term : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ w.[witness, go!"id"] ↦□ id ∗
      ownWMsg mv μ }}
    (App (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"handleHeartbeat"))
      (Val #mv)) (Val #term))
  {{ (ml : Loc), RET #ml;
      msgOwn ml (DFrac.own 1) ⟨(wHeartbeat id term μ).1, [], none, (wHeartbeat id term μ).2, []⟩ }}

end spec

end EtcdGrove
end Perennial
