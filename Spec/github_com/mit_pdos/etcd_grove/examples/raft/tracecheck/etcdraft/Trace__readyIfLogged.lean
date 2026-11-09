/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.readyIfLogged(ts, i)`, `ReadyIfLogged(i)`.
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

/-- `t.readyIfLogged(ts, i)`, of a server of the state whose pending messages are distinct and whose
bags' counts sum below `2^63` (`Ready`'s premises): `tr.readyIfLogged ts i`'s successors. -/
abbrev Trace.readyIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ uint.nat i ∈ ts.s.server ∧ (ts.s.pendingMessages.map Prod.fst).Nodup ∧
        (((ts.s.pendingMessages.map Prod.snd).sum + (ts.s.messages.map Prod.snd).sum : Nat) : Int) < 2 ^ 63⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"readyIfLogged")) (Val #g)) (Val #i))
  {{ (out : GoSlice), RET #out; statesOut out (tr.readyIfLogged ts (uint.nat i)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
