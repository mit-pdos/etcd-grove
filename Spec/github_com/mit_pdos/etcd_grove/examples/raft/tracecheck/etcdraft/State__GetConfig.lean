/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08, `notes/trace-validation-plan.md`,
"Probe set"): `State.GetConfig(i)`: server `i`'s configuration's incoming voters (`GetConfig(i)`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

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

/-- `s.GetConfig(i)`, of a server of the state: `getConfig i`. -/
abbrev State.GetConfig.spec : Prop :=
  ∀ (p : Loc) (st : State) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ ⌜uint.nat i ∈ st.server⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"GetConfig")) (Val #i))
  {{ (sl : GoSlice), RET #sl; setRO sl (st.getConfig (uint.nat i)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
