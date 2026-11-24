/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.VoteOf(vt, vf, t)`: B 99, `State.voteOf`.
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

/-- B 99 `VoteOf(vt, vf, t)`: `State.voteOf`. -/
abbrev State.VoteOf.spec : Prop :=
  ∀ (p : Loc) (s : State) (vt : w64) (vf : Str) (t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s }}
    (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"VoteOf")) (Val #vt)) (Val #vf)) (Val #t))
  {{ RET #(s.voteOf (sint.Z vt) vf (sint.Z t)); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
