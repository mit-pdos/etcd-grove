/-
Lean-first (no Rocq counterpart): `StateType.String` (`raft.go`), a role's name, which the traced
`traceEvent` reads (`r.state.String()`, every event's `role`; Q8 stage 1, slice 2, 2026-11-09).
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

/-- `st.String()` of a role's state value (`stateW64 ro`, the four `StateType` constants): the
role's name (`roleStr`, `stmap[st]`, read from the package fact). Another value is past `stmap`'s
four names, where Go panics; raft's state is always a role's (`ownRaftPhysCV`'s `Hstate`). -/
abbrev StateType.String.spec : Prop :=
  ∀ (ro : PRole),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val ((stateW64 ro) @!! StateType.ty @!! go!"String")) (Val #()))
  {{ RET #(roleStr ro); True }}

end spec

end EtcdGrove
end Perennial
