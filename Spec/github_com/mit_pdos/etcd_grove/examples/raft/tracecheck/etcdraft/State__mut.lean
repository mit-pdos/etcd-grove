/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08, `notes/trace-validation-plan.md`,
"Probe set"): `State.mut(i)`: server `i` of a clone, copied (the copy returned, held apart from the clone).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `s.mut(i)`, of a server `i` of a clone: a fresh copy of it, held apart (a server copied
already, `i ∈ M`, is copied again: the Go calls `mut` twice on one server in `reconfigure` and
`ApplySimpleConfChange`; review round 4 of layer C, F1). -/
abbrev State.mut.spec : Prop :=
  ∀ (p : Loc) (st : State) (M : List ID) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateOwn p st M ∗ ⌜uint.nat i ∈ st.server⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"mut")) (Val #i))
  {{ (c : Loc), RET #c; stateOwnHole p st M (uint.nat i) c ∗ serverOwn c (st.s (uint.nat i)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
