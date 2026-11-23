/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `confsAfterCount(l, a)`.
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

/-- R 171 `Cardinality(ConfsAfter(l, a))`: `confsAfterCount`, where defined. -/
abbrev confsAfterCount.spec : Prop :=
  ∀ (sl : GoSlice) (l : List Entry) (a : w64) (k : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      logRO sl l ∗ ⌜confsAfterCount l (sint.Z a) = .ok k⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.confsAfterCount)) (Val #sl)) (Val #a))
  {{ (w : w64), RET #w; ⌜sint.Z w = k⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
