/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.queued(n, ev)`: B 441, 452, `State.queued`.
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

/-- The item of a `ready`/`mem` report (B 441, 452): `State.queued`, where defined. -/
abbrev State.queued.spec : Prop :=
  ∀ (p : Loc) (s : State) (n : w64) (e : Loc) (ev : Event) (q : QItem),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗
      eventRO e ev ∗
      ⌜0 ≤ sint.Z n ∧ sint.Z n < s.cfg.server.length ∧ s.queued (sint.nat n) ev = .ok q⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"queued")) (Val #n)) (Val #e))
  {{ (u : G.QItem), RET #u; qitemRO u q }}

end spec

end AntCheck
end EtcdGrove
end Perennial
