/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `leadersAdd(s, l)`: `lset.add`.
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

/-- `s \cup {l}`: `lset.add`. -/
abbrev leadersAdd.spec : Prop :=
  ∀ (sl : GoSlice) (xs : List LeaderRec) (g : G.LeaderRec) (x : LeaderRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      leadersRO sl xs ∗ ⌜g.Server' = x.server ∧ sint.Z g.Term' = x.term ∧ (xs.length : Int) + 1 < 2 ^ 63⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.leadersAdd)) (Val #sl)) (Val #g))
  {{ (u : GoSlice), RET #u; leadersRO u (lset.add xs x) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
