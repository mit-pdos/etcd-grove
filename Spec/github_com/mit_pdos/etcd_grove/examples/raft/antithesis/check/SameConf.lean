/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `SameConf(ev, c)`: B 142-143, `sameConf`.
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

/-- B 142-143 `SameConf(ev, C)`: `sameConf`, where defined (the report's sets within `SetOf`'s premise). -/
abbrev SameConf.spec : Prop :=
  ∀ (e : Loc) (ev : Event) (g : G.Conf) (c : Conf) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      eventRO e ev ∗
      confRO g c ∗
      ⌜sameConf ev c = .ok b ∧ (ev.size : Int) < 2 ^ 62⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SameConf)) (Val #e)) (Val #g))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
