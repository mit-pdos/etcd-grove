/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.Garbage()`: B 696-706, `State.garbage`.
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

/-- B 696-706 `Garbage`: `State.garbage`, where defined. -/
abbrev State.Garbage.spec : Prop :=
  ∀ (p : Loc) (s : State) (gs : List Fact),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗
      ⌜s.garbage = .ok gs⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"Garbage")) (Val #()))
  {{ (u : GoSlice), RET #u; factsRO u gs }}

end spec

end AntCheck
end EtcdGrove
end Perennial
