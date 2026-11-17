/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `State.Committed(i)`: `Committed(i)`
(`State.committed`) where it is defined.
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

/-- `s.Committed(i)`, of a server `i` of the state: `Committed(i)`, sharing the log's array, where
it is defined (`SubSeq(log[i], 1, commitIndex[i])`; where it is not, TLC fails and the Go panics
with an `EvalError`, which a triple cannot state: `SubSeq`'s premise). -/
abbrev State.Committed.spec : Prop :=
  ∀ (p : Loc) (st : State) (i : w64) (c : List Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ ⌜uint.nat i ∈ st.server ∧ st.committed (uint.nat i) = .ok c⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"Committed")) (Val #i))
  {{ (u : GoSlice), RET #u; logRO u c }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
