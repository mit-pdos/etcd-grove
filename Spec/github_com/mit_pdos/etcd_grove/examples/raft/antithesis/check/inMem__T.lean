/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `x.T()`: B 214-253, `InMem.T`.
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

/-- `InMem`'s `T` (B 214-253): `InMem.T`, where defined. -/
abbrev inMem.T.spec : Prop :=
  ∀ (g : G.inMem) (x : InMem) (v : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      inMemRO g x ∗
      ⌜x.T = .ok v⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.ty @!! go!"T")) (Val #()))
  {{ (u : w64), RET #u; ⌜sint.Z u = v⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
