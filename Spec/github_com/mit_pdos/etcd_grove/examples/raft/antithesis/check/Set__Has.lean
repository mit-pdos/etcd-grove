/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `s.Has(x)`.
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

/-- `x \in s`. -/
abbrev Set.Has.spec : Prop :=
  ∀ (sl : GoSlice) (xs : SSet) (x : Str),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      strsRO sl xs }}
    (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set''.ty @!! go!"Has")) (Val #x))
  {{ RET #(SSet.has xs x); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
