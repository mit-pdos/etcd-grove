/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `votesHas(s, x)`.
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

/-- `x \in s` (Go's `==`). -/
abbrev votesHas.spec : Prop :=
  ∀ (sl : GoSlice) (xs : List VoteRec) (g : G.VoteRec) (x : VoteRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      votesRO sl xs ∗ ⌜voteRel g x⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesHas)) (Val #sl)) (Val #g))
  {{ RET #(xs.contains x); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
