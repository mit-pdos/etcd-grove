/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.Boot(n, ev)`: B 162-194, `State.boot`.
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

/-- `s.Boot(n, ev)` (B 162-194): `State.boot`'s successor (`ActionSpec`). -/
abbrev State.Boot.spec : Prop :=
  ActionSpec (GF := GF) go!"Boot" State.boot

end spec

end AntCheck
end EtcdGrove
end Perennial
