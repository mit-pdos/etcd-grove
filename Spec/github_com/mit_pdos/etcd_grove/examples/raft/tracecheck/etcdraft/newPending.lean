/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `newPending(s, s2, p)`, `\E m \in DOMAIN pendingMessages' : p(m) /\ OneMoreMessage(m)`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceRead

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

/-- `newPending(s, s2, f)`, of a closure `f` computing `P` on a message: `newPending s s2 P`. -/
abbrev newPending.spec : Prop :=
  ∀ (p : Loc) (s : State) (p2 : Loc) (s2 : State) (f : GoFunc) (P : Msg → Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p s ∗ stateRO p2 s2 ∗
      □ (∀ (q : Loc) (m : Msg), {{ msgRO q m }} (App (Val #f) (Val #q)) {{ RET #(P m); True }}) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.newPending))
      (Val #p)) (Val #p2)) (Val #f))
  {{ RET #(newPending s s2 P); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
