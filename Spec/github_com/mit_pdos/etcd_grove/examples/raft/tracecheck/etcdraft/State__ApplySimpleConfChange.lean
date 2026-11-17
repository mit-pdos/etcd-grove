/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.ApplySimpleConfChange(i)`: the action
`ApplySimpleConfChange(i)`.
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

/-- `s.ApplySimpleConfChange(i)`, of a server `i` of the state whose log is far from overflow (the Go's
loop index runs to the commit index plus one) and whose reconfiguration count can take one more, where
the Lean evaluates (`= .ok o`: the Go panics with an `EvalError` where TLC fails, a commit index past
the log): `o`, a new read-only state, or `nil` where the action is not enabled. -/
abbrev State.ApplySimpleConfChange.spec : Prop :=
  ∀ (p : Loc) (st : State) (i : w64) (o : Option State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗
      ⌜uint.nat i ∈ st.server ∧ (st.s (uint.nat i)).log.length < 2 ^ 62 ∧ st.reconfigCount + 1 < 2 ^ 63 ∧
        st.applySimpleConfChange (uint.nat i) = .ok o⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"ApplySimpleConfChange")) (Val #i))
  {{ (q : Loc), RET #q;
      match o with
      | none => ⌜q = null⌝
      | some st' => stateRO q st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
