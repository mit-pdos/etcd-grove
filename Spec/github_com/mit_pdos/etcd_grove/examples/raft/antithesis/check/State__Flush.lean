/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.Flush(n, ev)`: B 474-478, `State.flush`.
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

/-- `s.Flush(n, ev)` (B 474-478): `State.flush`'s successor (`ActionSpec`). -/
abbrev State.Flush.spec : Prop :=
  ActionSpec (GF := GF) go!"Flush" State.flush

end spec

end AntCheck
end EtcdGrove
end Perennial
