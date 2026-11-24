/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.OldVotes()`: B 708, `State.oldVotes`.
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

/-- B 708 `OldVotes`: `State.oldVotes`, where defined. -/
abbrev State.OldVotes.spec : Prop :=
  ∀ (p : Loc) (s : State) (vs : List VoteRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗
      ⌜s.oldVotes = .ok vs⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"OldVotes")) (Val #()))
  {{ (u : GoSlice), RET #u; votesRO u vs }}

end spec

end AntCheck
end EtcdGrove
end Perennial
