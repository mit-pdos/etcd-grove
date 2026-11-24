/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.SnapEv(n, ev)`: B 647-650, `State.snapEv`.
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

/-- `s.SnapEv(n, ev)` (B 647-650): `State.snapEv`'s successor (`ActionSpec`). -/
abbrev State.SnapEv.spec : Prop :=
  ActionSpec (GF := GF) go!"SnapEv" State.snapEv

end spec

end AntCheck
end EtcdGrove
end Perennial
