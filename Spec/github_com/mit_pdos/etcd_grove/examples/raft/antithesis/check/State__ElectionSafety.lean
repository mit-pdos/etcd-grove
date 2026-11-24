/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `s.ElectionSafety()`.
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

/-- R 581-582 `ElectionSafety`. -/
abbrev State.ElectionSafety.spec : Prop :=
  ∀ (p : Loc) (s : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"ElectionSafety")) (Val #()))
  {{ RET #s.electionSafety; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
