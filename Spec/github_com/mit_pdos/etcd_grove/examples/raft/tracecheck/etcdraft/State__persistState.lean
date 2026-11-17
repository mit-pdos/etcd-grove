/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.persistState(i)`: `PersistState(i)`, on a clone being built.
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

/-- `s.persistState(i)` on a clone being built, of a server of the state: `persistState i`; server
`i` is then a copy being written. -/
abbrev State.persistState.spec : Prop :=
  ∀ (p : Loc) (st : State) (M : List ID) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateOwn p st M ∗ ⌜uint.nat i ∈ st.server⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"persistState")) (Val #i))
  {{ RET #(); stateOwn p (st.persistState (uint.nat i)) (uint.nat i :: M) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
