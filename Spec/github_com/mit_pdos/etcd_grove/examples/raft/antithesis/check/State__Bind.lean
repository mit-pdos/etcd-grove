/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.Bind(n, ev)`: B 669-686, `State.bind`.
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

/-- `s.Bind(n, ev)` (B 669-686): `State.bind`'s successor (`ActionSpec`). -/
abbrev State.Bind.spec : Prop :=
  ActionSpec (GF := GF) go!"Bind" State.bind

end spec

end AntCheck
end EtcdGrove
end Perennial
