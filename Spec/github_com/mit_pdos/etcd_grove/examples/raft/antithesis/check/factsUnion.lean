/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `factsUnion(s, t)`: `lset.union`.
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

/-- `s \cup t`: `lset.union`. -/
abbrev factsUnion.spec : Prop :=
  ∀ (sl : GoSlice) (xs : List Fact) (tl : GoSlice) (ys : List Fact),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      factsRO sl xs ∗ factsRO tl ys ∗ ⌜(xs.length : Int) + ys.length < 2 ^ 62⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsUnion)) (Val #sl)) (Val #tl))
  {{ (u : GoSlice), RET #u; factsRO u (lset.union xs ys) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
