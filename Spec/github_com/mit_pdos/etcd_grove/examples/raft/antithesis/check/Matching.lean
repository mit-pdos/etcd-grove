/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `Matching(a, b)`: B 132-134, `matching`.
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

/-- B 132-134 `Matching(a, b)`: `matching`, where defined (`a` shorter than the Go `int`'s maximum, so the loop's `k++` does not wrap). -/
abbrev Matching.spec : Prop :=
  ∀ (al : GoSlice) (a : List Entry) (bl : GoSlice) (b : List Entry) (r : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      logRO al a ∗
      logRO bl b ∗
      ⌜matching a b = .ok r ∧ (a.length : Int) < 2 ^ 63 - 1⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Matching)) (Val #al)) (Val #bl))
  {{ RET #r; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
