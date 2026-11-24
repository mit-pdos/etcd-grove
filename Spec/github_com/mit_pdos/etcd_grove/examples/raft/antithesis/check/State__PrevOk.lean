/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `s.PrevOk(j, m)`.
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

/-- R 366-369 `PrevOk(j, m)`: `State.prevOk`, where defined. -/
abbrev State.PrevOk.spec : Prop :=
  ∀ (p : Loc) (s : State) (j : w64) (g : G.AppendFact) (m : AppendFact) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗ appendFactRO g m ∗
      ⌜0 ≤ sint.Z j ∧ sint.Z j < s.cfg.server.length ∧ s.prevOk (sint.nat j) m = .ok b⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"PrevOk")) (Val #j)) (Val #g))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
