/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `s.Equal(t)`.
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

/-- `s = t` (elementwise: as lists). -/
abbrev Set.Equal.spec : Prop :=
  ∀ (sl : GoSlice) (xs : SSet) (tl : GoSlice) (ys : SSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      strsRO sl xs ∗ strsRO tl ys }}
    (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set''.ty @!! go!"Equal")) (Val #tl))
  {{ RET #(decide (xs = ys)); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
