/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `Lowest(a, b)`: B 288, `lowest`.
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

/-- B 288 `Lowest(a, b)`: `lowest`. -/
abbrev Lowest.spec : Prop :=
  ∀ (a b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Lowest)) (Val #a)) (Val #b))
  {{ (u : w64), RET #u; ⌜sint.Z u = lowest (sint.Z a) (sint.Z b)⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
