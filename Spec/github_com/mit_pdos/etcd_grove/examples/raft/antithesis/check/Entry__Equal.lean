/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): `e.Equal(f)`: `Entry.equal` where it is defined.
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

/-- `e.Equal(f)`: `Entry.equal x y`, where it is defined. -/
abbrev Entry.Equal.spec : Prop :=
  ∀ (e : G.Entry) (x : Entry) (f : G.Entry) (y : Entry) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      entryRO e x ∗ entryRO f y ∗ ⌜x.equal y = .ok b⌝ }}
    (App (Val (e @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry.ty @!! go!"Equal")) (Val #f))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
