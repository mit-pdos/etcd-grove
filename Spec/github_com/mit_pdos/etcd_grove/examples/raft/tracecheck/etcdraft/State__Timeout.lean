/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08, `notes/trace-validation-plan.md`,
"Probe set"): `State.Timeout(i)`, the action `Timeout(i)`: the hard probe (the copy-on-write discipline).
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

/-- `s.Timeout(i)`, of a server of the state whose term is far from overflow: `timeout i`'s
successor, a new read-only state, or `nil` where it is not enabled. -/
abbrev State.Timeout.spec : Prop :=
  ∀ (p : Loc) (st : State) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗
      ⌜uint.nat i ∈ st.server ∧ st.server.Nodup ∧ numOk (st.s (uint.nat i)).currentTerm⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"Timeout")) (Val #i))
  {{ (q : Loc), RET #q;
      match st.timeout (uint.nat i) with
      | none => ⌜q = null⌝
      | some st' => stateRO q st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
