/-
Lean-first (no Rocq counterpart): `stateMachineEventType.String` (`state_trace.go`), the event's
name in a traced event (Q8 stage 1, slice 2, 2026-11-09).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedCap

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

/-- `e.String()`: the name of the event `e` (`evtNames`, the slice literal's 19 names, indexed by
the constant). Go panics past the names (the index out of range), hence the premise. -/
abbrev stateMachineEventType.String.spec : Prop :=
  ∀ (e : w64), uint.nat e < evtNames.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val (e @!! stateMachineEventType.ty @!! go!"String")) (Val #()))
  {{ (str : GoString), RET #str; ⌜evtNames[uint.nat e]? = some str⌝ }}

end spec

end EtcdGrove
end Perennial
