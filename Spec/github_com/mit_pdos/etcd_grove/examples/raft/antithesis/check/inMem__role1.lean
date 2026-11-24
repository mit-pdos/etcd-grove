/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `x.role1()`: B 214-253, `InMem.role1`.
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

/-- `InMem`'s `role1` (B 214-253): `InMem.role1`, where defined. -/
abbrev inMem.role1.spec : Prop :=
  ∀ (g : G.inMem) (x : InMem) (v : Str),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      inMemRO g x ∗
      ⌜x.role1 = .ok v⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.ty @!! go!"role1")) (Val #()))
  {{ RET #v; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
