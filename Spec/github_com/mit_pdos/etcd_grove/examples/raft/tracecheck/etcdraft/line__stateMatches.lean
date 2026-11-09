/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `ln.stateMatches(s, i)`, what `ValidatePreStates`/`ValidatePostStates` check of server `i`.
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

/-- `ln.stateMatches(s, i)`: `x.stateMatches st i`. -/
abbrev line.stateMatches.spec : Prop :=
  ∀ (q : Loc) (x : Line) (p : Loc) (st : State) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      linePtrRO q x ∗ stateRO p st }}
    (App (App (Val (q @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line.ty
      @!! go!"stateMatches")) (Val #p)) (Val #i))
  {{ RET #(x.stateMatches st (uint.nat i)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
