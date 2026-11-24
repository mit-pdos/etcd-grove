/- Lean-first (no Rocq counterpart).

`work(c, ids)`: at most 8 random operations (`below(9)`), each a random section; one credit of the id counter each.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ClientDefs

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
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- See the file header. -/
abbrev work.spec : Prop :=
  ∀ (γid γb : GName) (c : GoInterface) (ids : Loc),
  {{ drvCli γid γb c ids ∗ ownToks γb 8 }}
    (App (App (Val (@! work)) (Val #c)) (Val #ids))
  {{ RET #(); True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
