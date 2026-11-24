/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.ConfEv(n, ev)`: B 614-630, `State.confEv`.
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

/-- `s.ConfEv(n, ev)` (B 614-630): `State.confEv`'s successor (`ActionSpec`). -/
abbrev State.ConfEv.spec : Prop :=
  ActionSpec (GF := GF) go!"ConfEv" State.confEv

end spec

end AntCheck
end EtcdGrove
end Perennial
