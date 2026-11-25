/- Lean-first (no Rocq counterpart).

`(*counter).take()`: a fresh id, with its token (`Defs.lean`), for one credit.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
abbrev counter.take.spec : Prop :=
  ∀ (γid γb : GName) (c : Loc),
  {{ isCtr γid γb c ∗ ownToks γb 1 }}
    (App (Val (c @!! go.GoType.PointerType counter.ty @!! go!"take")) (Val #()))
  {{ (id : w64), RET #id; idTok γid id }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
