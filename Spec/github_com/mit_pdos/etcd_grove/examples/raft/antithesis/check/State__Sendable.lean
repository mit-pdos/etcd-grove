/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.Sendable(f)`: B 128, `State.sendable`.
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

/-- B 128 `Sendable(f)`: `State.sendable`, where defined (as `SendableIn`). -/
abbrev State.Sendable.spec : Prop :=
  ∀ (p : Loc) (s : State) (g : G.AppendFact) (f : AppendFact) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗
      appendFactRO g f ∗
      ⌜s.sendable f = .ok b ∧ bigOk f.prevLogIndex ∧ (f.entries.length : Int) < 2 ^ 62⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"Sendable")) (Val #g))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
