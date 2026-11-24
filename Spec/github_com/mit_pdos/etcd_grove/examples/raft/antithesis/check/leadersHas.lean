/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `leadersHas(s, l)`.
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

/-- `l \in s` (Go's `==`). -/
abbrev leadersHas.spec : Prop :=
  ∀ (sl : GoSlice) (xs : List LeaderRec) (g : G.LeaderRec) (x : LeaderRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      leadersRO sl xs ∗ ⌜g.Server' = x.server ∧ sint.Z g.Term' = x.term⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.leadersHas)) (Val #sl)) (Val #g))
  {{ RET #(xs.contains x); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
