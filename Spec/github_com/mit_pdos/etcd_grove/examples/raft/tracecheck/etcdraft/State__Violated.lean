/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `State.Violated()`: the first invariant
violated (`State.violated`) where every invariant it evaluates is defined.
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

/-- `s.Violated()`: the name of the first invariant `Traceetcdraft.cfg` checks that `s` violates, or
`""` (`State.violated`), where the invariants it evaluates are defined (where one is not, TLC fails
and the Go panics with an `EvalError`, which a triple cannot state). The logs shorter than
`2^63 - 1` and the configurations smaller than `2^62` (the invariants' premises). -/
abbrev State.Violated.spec : Prop :=
  ∀ (p : Loc) (st : State) (r : Option String),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗
      ⌜(∀ i ∈ st.server, ((st.s i).log.length : Int) < 2 ^ 63 - 1) ∧
        (∀ i ∈ st.server, (st.getConfig i).length < 2 ^ 62) ∧ st.violated = .ok r⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"Violated")) (Val #()))
  {{ (v : GoString), RET #v; ⌜strRel v (r.getD "")⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
