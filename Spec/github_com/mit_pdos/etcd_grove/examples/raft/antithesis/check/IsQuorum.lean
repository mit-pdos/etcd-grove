/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `IsQuorum(s, c)`.
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

/-- R 129 `IsQuorum(S, C)`: `isQuorum`. -/
abbrev IsQuorum.spec : Prop :=
  ∀ (sl : GoSlice) (xs : SSet) (g : G.Conf) (c : Conf),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      strsRO sl xs ∗ confRO g c ∗ ⌜(xs.length : Int) < 2 ^ 61 ∧ (c.cin.length : Int) < 2 ^ 61 ∧ (c.cout.length : Int) < 2 ^ 61⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsQuorum)) (Val #sl)) (Val #g))
  {{ RET #(isQuorum xs c); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
