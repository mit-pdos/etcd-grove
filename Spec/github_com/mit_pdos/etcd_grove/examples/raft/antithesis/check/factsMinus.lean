/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `factsMinus(s, t)`: `lset.minus`.
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

/-- `s \ t`: `lset.minus`. -/
abbrev factsMinus.spec : Prop :=
  ∀ (sl : GoSlice) (xs : List Fact) (tl : GoSlice) (ys : List Fact),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      factsRO sl xs ∗ factsRO tl ys }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsMinus)) (Val #sl)) (Val #tl))
  {{ (u : GoSlice), RET #u; factsRO u (lset.minus xs ys) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
