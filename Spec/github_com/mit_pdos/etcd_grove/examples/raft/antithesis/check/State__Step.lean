/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.Step(ev)`: B 766-772, `State.step`.
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

/-- B 766-772 `Step` (without its guard): `State.step`'s successor, owned (its `I` one more), where defined, within budget. -/
abbrev State.Step.spec : Prop :=
  ∀ (p : Loc) (s : State) (e : Loc) (ev : Event) (o : Option State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗
      eventRO e ev ∗
      ⌜s.BoundedFor ev ∧ s.step ev = .ok o⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"Step")) (Val #e))
  {{ (q : Loc) (ok : Bool), RET (PairV #q #ok); succOwn q ok o }}

end spec

end AntCheck
end EtcdGrove
end Perennial
