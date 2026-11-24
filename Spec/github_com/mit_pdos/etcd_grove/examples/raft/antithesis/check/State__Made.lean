/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `s.Made(n, ev)`: B 496-499, `State.made`.
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

/-- `s.Made(n, ev)` (B 496-499): `State.made`'s successor (`ActionSpec`). -/
abbrev State.Made.spec : Prop := ActionSpec (GF := GF) go!"Made" State.made

end spec

end AntCheck
end EtcdGrove
end Perennial
