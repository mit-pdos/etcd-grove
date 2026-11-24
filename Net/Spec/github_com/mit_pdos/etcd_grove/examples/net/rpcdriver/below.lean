/- Lean-first (no Rocq counterpart).

`below(n)`: a random number in `[0, n)`, `0` if `n` is `0`.
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
abbrev below.spec : Prop :=
  ∀ (n : w64),
  {{ (True : IProp GF) }}
    (App (Val (@! below)) (Val #n))
  {{ (r : w64), RET #r; ⌜(n = W64 0 → r = W64 0) ∧ (n ≠ W64 0 → uint.Z r < uint.Z n)⌝ }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
