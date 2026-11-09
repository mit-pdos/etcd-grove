/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.commitTo(i, c)`: `CommitTo(i, c)`, on a clone being built.
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

/-- `s.commitTo(i, c)` on a clone being built, of a server of the state: `commitTo i c`; server `i`
is then a copy being written. -/
abbrev State.commitTo.spec : Prop :=
  ∀ (p : Loc) (st : State) (M : List ID) (i c : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateOwn p st M ∗ ⌜uint.nat i ∈ st.server⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"commitTo")) (Val #i)) (Val #c))
  {{ RET #(); stateOwn p (st.commitTo (uint.nat i) (sint.Z c)) (uint.nat i :: M) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
