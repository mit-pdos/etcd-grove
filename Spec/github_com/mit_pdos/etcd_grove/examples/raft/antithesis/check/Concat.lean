/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `Concat(a, b)`: `a ++ b`.
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

/-- `a \o b`, a new slice. -/
abbrev Concat.spec : Prop :=
  ∀ (al : GoSlice) (a : List Entry) (bl : GoSlice) (b : List Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      logRO al a ∗ logRO bl b ∗ ⌜(a.length : Int) + b.length < 2 ^ 63⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Concat)) (Val #al)) (Val #bl))
  {{ (u : GoSlice), RET #u; logRO u (a ++ b) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
