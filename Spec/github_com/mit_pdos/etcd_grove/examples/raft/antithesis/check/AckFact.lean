/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `AckFact(src, dst, t, k)`: B 73, `ackFact`.
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

/-- B 73 `AckFact(src, dst, t, k)`: `ackFact`. -/
abbrev AckFact.spec : Prop :=
  ∀ (src dst : Str) (t k : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.AckFact)) (Val #src)) (Val #dst)) (Val #t)) (Val #k))
  {{ (u : G.Fact), RET #u; ⌜factRel u (ackFact src dst (sint.Z t) (sint.Z k))⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
