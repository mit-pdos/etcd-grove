/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `Recovered(ev, t, v, c, l)`: B 155-157, `recovered`.
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

/-- B 155-157 `Recovered(ev, t, v, c, l)`: `recovered`, where defined. -/
abbrev Recovered.spec : Prop :=
  ∀ (e : Loc) (ev : Event) (t : w64) (v : Str) (c : w64) (ll : GoSlice) (l : List Entry) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      eventRO e ev ∗
      logRO ll l ∗
      ⌜recovered ev (sint.Z t) v (sint.Z c) l = .ok b⌝ }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Recovered)) (Val #e)) (Val #t)) (Val #v)) (Val #c)) (Val #ll))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
