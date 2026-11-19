/- Lean-first (no Rocq counterpart).

# `k8s/authz`: the definitions its top-level statement is written in

The program the example's top-level theorem is about: the driver package's initialization (which
initializes its imports, `k8s.io/apiserver`'s `authorization/{authorizer,union}` among them), then
`Main()`. In a defs module so that the statement (`Spec/.../TopLevelRobustness.lean`) imports no
proof (CLAUDE.md, "Import tiers").
-/
module

public import Code.github_com.mit_pdos.etcd_grove.examples.k8s.authz
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section program

variable [go_gctx : GoGlobalContext]

/-- The conditional-authorization driver's program: the package's initialization, then `Main()`,
which runs one request through the two phases over a union of arbitrary leaf authorizers and
panics unless C1-C3 hold (`examples/k8s/authz/authz.go`). -/
def authzProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.authz.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.k8s.authz.Main) #()

end program
end k8s_authz
end EtcdGrove
end Perennial

end

end
