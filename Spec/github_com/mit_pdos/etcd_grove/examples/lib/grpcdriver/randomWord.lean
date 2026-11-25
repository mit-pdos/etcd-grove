/- Lean-first (no Rocq counterpart).

`randomWord()`: a random word (`wordOk`: at most 16 letters).
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
abbrev randomWord.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! randomWord)) (Val #()))
  {{ (w : GoString), RET #w; ⌜wordOk w⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
