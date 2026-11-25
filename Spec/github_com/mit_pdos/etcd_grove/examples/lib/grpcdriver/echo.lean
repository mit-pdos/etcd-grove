/- Lean-first (no Rocq counterpart).

`echo(c, ids)`: the section unary-reply (`grpcdriver.go`); it returns (its checks never panic), with one credit of the id counter.
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
abbrev echo.spec : Prop :=
  ∀ (γid γb : GName) (c : GoInterface) (ids : Loc),
  {{ drvCli (GF := GF) γid γb c ids ∗ ownToks γb 1 }}
    (App (App (Val (@! echo)) (Val #c)) (Val #ids))
  {{ RET #(); True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
