/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `c.Equal(d)`.
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

/-- `C = D`. -/
abbrev Conf.Equal.spec : Prop :=
  ∀ (g : G.Conf) (c : Conf) (h : G.Conf) (d : Conf),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      confRO g c ∗ confRO h d }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Conf.ty @!! go!"Equal")) (Val #h))
  {{ RET #(decide (c = d)); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
