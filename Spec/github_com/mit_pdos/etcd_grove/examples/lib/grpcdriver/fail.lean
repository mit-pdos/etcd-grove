/- Lean-first (no Rocq counterpart).

`fail(c, ids)`: the section status-roundtrip (`grpcdriver.go`); it returns (its checks never panic), with one credit of the id counter.
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
abbrev fail.spec : Prop :=
  ∀ (γid γb : GName) (c : GoInterface) (ids : Loc),
  {{ drvCli γid γb c ids ∗ ownToks γb 1 }}
    (App (App (Val (@! fail)) (Val #c)) (Val #ids))
  {{ RET #(); True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
