/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.InMemory(n, ev)`: B 213-275, `State.inMemory`.
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

/-- B 213-275 `InMemory(n, ev)`: `State.inMemory`'s record, where defined, within budget (`State.BoundedFor`). -/
abbrev State.InMemory.spec : Prop :=
  ∀ (p : Loc) (s : State) (n : w64) (e : Loc) (ev : Event) (r : MemResult),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗
      eventRO e ev ∗
      ⌜0 ≤ sint.Z n ∧ sint.Z n < s.cfg.server.length ∧ s.BoundedFor ev ∧ s.inMemory (sint.nat n) ev = .ok r⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"InMemory")) (Val #n)) (Val #e))
  {{ (g : G.MemResult), RET #g; memResultRO g r }}

end spec

end AntCheck
end EtcdGrove
end Perennial
