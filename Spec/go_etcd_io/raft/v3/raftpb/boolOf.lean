/-
`boolOf(p)` (`raftpb/confstate.go`; the raft fork's fourth fix, premise fixes 2, 2026-11-10): an
optional bool field's value, an unset one read as `false`. Lean-first.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

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

/-- `boolOf(p)` of a bool cell holding `v` (`cellRO`: `nil`, read as `false`, or read-only) is `v`. -/
abbrev raftpb.boolOf.spec : Prop :=
  ∀ (p : Loc) (v : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ cellRO p v }}
    (App (Val #(functions raftpb.boolOf [])) (Val #p))
  {{ RET #v; True }}

end spec

end EtcdGrove
end Perennial
