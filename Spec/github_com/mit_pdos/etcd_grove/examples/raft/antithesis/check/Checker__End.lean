/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `c.End()`: `check.go`, `Checker.finish`.
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

/-- The verdict once the stream has ended: `Checker.finish` (a checker without a verdict within budget: `I - 1`). -/
abbrev Checker.End.spec : Prop :=
  ∀ (p : Loc) (c : Checker),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      checkerOwn p c ∗
      ⌜c.done = false → c.state.Bounded⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Checker.ty @!! go!"End")) (Val #()))
  {{ (r : G.Verdict), RET #r; verdictRO r c.finish ∗ checkerOwn p c }}

end spec

end AntCheck
end EtcdGrove
end Perennial
