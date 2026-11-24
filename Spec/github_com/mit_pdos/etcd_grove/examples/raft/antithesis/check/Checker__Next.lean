/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `c.Next(ev)`: `check.go`, `Checker.next`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- Takes the next report: `Checker.next`, where defined; a checker without a verdict is within budget for the report (its `GC` steps keep it: `GCWithin`). -/
abbrev Checker.Next.spec : Prop :=
  ∀ (p : Loc) (c : Checker) (e : Loc) (ev : Event) (c' : Checker),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      checkerOwn p c ∗
      eventRO e ev ∗
      ⌜(c.done = false → c.state.BoundedFor ev) ∧ c.next ev = .ok c'⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Checker.ty @!! go!"Next")) (Val #e))
  {{ RET #(); checkerOwn p c' }}

end spec

end AntCheck
end EtcdGrove
end Perennial
