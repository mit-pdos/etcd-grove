/- Lean-first (no Rocq counterpart).

`(*counter).take()`: a fresh id, with its token (`idTok`, `Svc.lean`), for one take credit
(`isCtr`, `Defs.lean`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
abbrev counter.take.spec : Prop :=
  ∀ (γid γb : GName) (c : Loc),
  {{ isCtr γid γb c ∗ ownToks γb 1 }}
    (App (Val (c @!! go.GoType.PointerType counter.ty @!! go!"take")) (Val #()))
  {{ (id : w64), RET #id; idTok γid id }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
