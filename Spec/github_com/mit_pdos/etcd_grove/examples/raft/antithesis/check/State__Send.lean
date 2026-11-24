/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.Send(n, ev)`: B 510-593, `State.send`.
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

/-- `s.Send(n, ev)` (B 510-593): `State.send`'s successor (`ActionSpec`). -/
abbrev State.Send.spec : Prop :=
  ActionSpec (GF := GF) go!"Send" State.send

end spec

end AntCheck
end EtcdGrove
end Perennial
