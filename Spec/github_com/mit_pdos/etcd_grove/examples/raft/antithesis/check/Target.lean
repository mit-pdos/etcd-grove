/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `Target(c, d)`.
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

/-- R 142 `Target(C, d)`: `target`, where defined (`d` a string: an `EvalError`). -/
abbrev Target.spec : Prop :=
  ∀ (g : G.Conf) (c : Conf) (h : G.Value) (d : Value) (t : SSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      confRO g c ∗ valueRO h d ∗ ⌜target c d = .ok t ∧ (c.cin.length : Int) + d.add.length < 2 ^ 61 ∧ (d.remove.length : Int) < 2 ^ 61⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Target)) (Val #g)) (Val #h))
  {{ (u : GoSlice), RET #u; strsRO u t }}

end spec

end AntCheck
end EtcdGrove
end Perennial
