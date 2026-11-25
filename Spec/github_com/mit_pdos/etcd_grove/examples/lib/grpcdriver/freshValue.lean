/- Lean-first (no Rocq counterpart).

`freshValue(ids)`: the fresh value of a fresh id (`mkVal`), with the id's token, for one credit.
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
abbrev freshValue.spec : Prop :=
  ∀ (γid γb : GName) (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
      isCtr γid γb c ∗ ownToks γb 1 }}
    (App (Val (@! freshValue)) (Val #c))
  {{ (v : GoString), RET #v; ∃ (id : w64) (w : GoString), ⌜v = mkVal id w ∧ wordOk w⌝ ∗
      idTok γid id }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
