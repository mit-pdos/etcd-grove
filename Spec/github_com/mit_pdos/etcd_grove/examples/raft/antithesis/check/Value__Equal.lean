/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): `v.Equal(w)`: `Value.equal` where it is defined.
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

/-- `v.Equal(w)`: `Value.equal v w`, where it is defined (a string compared with a record is an
`EvalError`). -/
abbrev Value.Equal.spec : Prop :=
  ∀ (g : G.Value) (v : Value) (h : G.Value) (w : Value) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      valueRO g v ∗ valueRO h w ∗ ⌜v.equal w = .ok b⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value.ty @!! go!"Equal")) (Val #h))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
