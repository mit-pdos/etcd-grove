/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `s.clone()`: a copy of the struct, owned, holding the same state.
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

/-- `s.clone()`: a new `*State` whose struct is a copy of `s`'s, owned (its fields are then set
by the action building a successor), holding the same Lean state. -/
abbrev State.clone.spec : Prop :=
  ∀ (p : Loc) (s : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty
      @!! go!"clone")) (Val #()))
  {{ (q : Loc), RET #q; stateOwn q s }}

end spec

end AntCheck
end EtcdGrove
end Perennial
