/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `Majority(s, v)`.
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

/-- R 127 `Majority(S, V)`: `majority` (the sets' sizes far from overflow). -/
abbrev Majority.spec : Prop :=
  ∀ (sl : GoSlice) (xs : SSet) (vl : GoSlice) (vs : SSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      strsRO sl xs ∗ strsRO vl vs ∗ ⌜(xs.length : Int) < 2 ^ 61 ∧ (vs.length : Int) < 2 ^ 61⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Majority)) (Val #sl)) (Val #vl))
  {{ RET #(majority xs vs); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
