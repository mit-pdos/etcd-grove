/-
`uint64Of(p)` (`raftpb/confstate.go`; the raft fork's fourth fix, premise fixes 2, 2026-11-10): an
optional uint64 field's value, an unset one read as `0` (the witness fork's `Witness` fields). Lean-first.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPb

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

/-- `uint64Of(p)` of a `uint64` cell holding `v` (`cellRO`: `nil`, read as `0`, or read-only) is `v`. -/
abbrev raftpb.uint64Of.spec : Prop :=
  ∀ (p : Loc) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ cellRO p v }}
    (App (Val #(functions raftpb.uint64Of [])) (Val #p))
  {{ RET #v; True }}

end spec

end EtcdGrove
end Perennial
