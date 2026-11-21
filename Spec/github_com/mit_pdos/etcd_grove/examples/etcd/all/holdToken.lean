/-
`holdToken()` (`examples/etcd/all/all.go`): sleeps forever. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

/-- `holdToken()` does not return (`False` after it): `spawn` runs it on a goroutine that holds no
resource and never ends, and keeps the token `wp_fork_tok_self` gives it (`k8s_all.holdToken.spec`). -/
abbrev holdToken.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.all }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.holdToken)) (Val #()))
  {{ RET #(); False }}

end spec

end etcd_all
end EtcdGrove
end Perennial
