/- Lean-first (no Rocq counterpart).

`randomArgs(ids)`: a request with a fresh id (its token), a payload of at most `maxData` (64)
bytes, and either no error to answer with or one of the method's messages.
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
abbrev randomArgs.spec : Prop :=
  ∀ (γid γb : GName) (c : Loc),
  {{ drvFacts ∗ isCtr γid γb c ∗ ownToks γb 1 }}
    (App (Val (@! randomArgs)) (Val #c))
  {{ (pa : Loc), RET #pa; ∃ (id : w64) (dsl : GoSlice) (data : List w8) (fail : GoString),
      pa ↦ service.Args.mk id dsl fail ∗ dsl ↦* data ∗ ⌜data.length ≤ 64⌝ ∗
      ⌜fail = [] ∨ fail ∈ failList⌝ ∗ idTok γid id }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
